// no_python: This activity-scoped adapter performs Android effects and feeds the proved Lean
// runtime.
package io.kotlean

import android.app.Activity
import android.app.Application
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ComponentCallbacks
import android.content.Context
import android.content.res.Configuration
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.util.Base64
import android.util.Log
import android.view.HapticFeedbackConstants
import android.widget.TextView
import java.math.BigInteger
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.charset.StandardCharsets
import java.util.ArrayDeque
import java.util.Collections
import java.util.IdentityHashMap

object Kotlean {
    private const val stateKey = "io.kotlean.saved-model"

    // Call after super.onCreate; the activity owns the resource and plugins. Close on the main
    // thread.
    fun run(activity: Activity, library: String, savedInstanceState: Bundle?,
        plugins: Map<String, PlatformPlugin> = emptyMap()): AutoCloseable {
        check(Looper.myLooper() == Looper.getMainLooper()) { "Kotlean.run requires the Android main thread" }
        check(activity.window.decorView.getTag(R.id.kotlean_owner) == null) { "This activity already owns a Kotlean session" }
        var host: Host? = null
        return try {
            System.loadLibrary(library)
            host = Host(activity, library, plugins.toMap())
            activity.window.decorView.setTag(R.id.kotlean_owner, host)
            host.start(savedInstanceState?.getByteArray(stateKey))
            host
        } catch (error: Throwable) {
            host?.close()
            failure(activity, error)
            AutoCloseable { }
        }
    }

    private fun failure(activity: Activity, error: Throwable) {
        Log.e("Kotlean", "Application failed", error)
        activity.setContentView(TextView(activity).apply {
            text = "Kotlean could not run this app.\n\n${error.message ?: error.javaClass.simpleName}"
            setPadding(32, 32, 32, 32)
        })
    }

    private class Host(private val activity: Activity, library: String,
        private val plugins: Map<String, PlatformPlugin>) : AutoCloseable,
        Application.ActivityLifecycleCallbacks, ComponentCallbacks {
        private val handler = Handler(Looper.getMainLooper())
        private val token = Any()
        private val queue = ArrayDeque<Event>()
        private var draining = false
        @Volatile private var closed = false
        private var lifecycleRegistered = false
        private var configurationRegistered = false
        private var native: NativeSession? = null
        private val renderer = AndroidRenderer(activity, ::dispatch)
        private class ActiveSubscription(val value: Subscription) { var callback: Runnable? = null }
        private val subscriptions = mutableMapOf<BigInteger, ActiveSubscription>()
        private var back: BackBridge? = null
        private val storage = activity.getSharedPreferences("kotlean.$library", Context.MODE_PRIVATE)

        fun start(snapshot: ByteArray?) {
            native = NativeSession(Wire.encodeInit(snapshot?.let(::Bytes)))
            back = BackBridge(activity, ::signal)
            activity.setContentView(renderer.content)
            activity.application.registerActivityLifecycleCallbacks(this)
            lifecycleRegistered = true
            activity.application.registerComponentCallbacks(this)
            configurationRegistered = true
            output(Wire.decodeOut(native!!.initialOutput))
            dispatch(Event.Lifecycle(false))
        }

        private fun post(action: () -> Unit) {
            if (!closed) handler.postAtTime({ if (!closed) action() }, token, SystemClock.uptimeMillis())
        }

        private fun dispatch(event: Event) {
            if (closed) return
            check(Looper.myLooper() == Looper.getMainLooper()) { "Platform events require the main thread" }
            queue.addLast(event)
            if (draining) return
            draining = true
            try {
                while (!closed && queue.isNotEmpty()) {
                    val bytes = try { Wire.encodeEvent(queue.removeFirst()) } catch (error: WireException) {
                        Log.e("Kotlean", "Invalid platform input", error)
                        continue
                    }
                    output(Wire.decodeOut(native!!.step(bytes)))
                }
            } catch (error: Exception) {
                close()
                failure(activity, error)
            } finally { draining = false }
        }

        private fun output(out: Out) {
            when (out) {
                is Out.Failed -> error(out.message)
                is Out.Ignored -> out.diagnostic?.let { Log.w("Kotlean", it) }
                is Out.Changes -> {
                    renderer.apply(out.value.patches, out.value.revision)
                    for (change in out.value.subscriptions) when (change) {
                        is SubscriptionChange.Remove -> {
                            val active = subscriptions[change.id]
                            if (active?.value?.generation == change.generation) {
                                active.callback?.let(handler::removeCallbacks)
                                subscriptions.remove(change.id)
                            }
                        }
                        is SubscriptionChange.Add -> {
                            val value = change.value
                            check(!subscriptions.containsKey(value.id)) { "Duplicate subscription id" }
                            val active = ActiveSubscription(value)
                            subscriptions[value.id] = active
                            val source = value.source
                            if (source is Source.Tick) {
                                val period = source.milliseconds.longValueExact()
                                val callback = object : Runnable {
                                    override fun run() {
                                        if (closed || subscriptions[value.id] !== active) return
                                        val timestamp = ByteBuffer.allocate(Long.SIZE_BYTES)
                                            .order(ByteOrder.LITTLE_ENDIAN)
                                            .putLong(SystemClock.uptimeMillis())
                                            .array()
                                        signal(value, timestamp)
                                        if (!closed && subscriptions[value.id] === active) {
                                            handler.postAtTime(this, token, Math.addExact(SystemClock.uptimeMillis(), period))
                                        }
                                    }
                                }
                                active.callback = callback
                                handler.postAtTime(callback, token, Math.addExact(SystemClock.uptimeMillis(), period))
                            }
                        }
                    }
                    if (out.value.subscriptions.isNotEmpty()) {
                        back?.update(subscriptions.values.map { it.value }.filter { it.source is Source.Back })
                    }
                    for (request in out.value.commands) command(request)
                }
            }
        }

        private fun signal(subscription: Subscription, payload: ByteArray = byteArrayOf()) {
            dispatch(Event.Subscription(subscription.generation, subscription.id, Bytes(payload)))
        }

        private fun answer(id: BigInteger, reply: Reply) { post { dispatch(Event.Answer(id, reply)) } }
        private fun errorReply(error: Throwable): Reply.Error {
            val text = error.message ?: error.javaClass.simpleName
            return Reply.Error(String(text.toByteArray(StandardCharsets.UTF_8), StandardCharsets.UTF_8))
        }

        private fun command(command: Command) {
            try {
                when (val effect = command.effect) {
                    is Effect.Delay -> {
                        handler.postAtTime({ answer(command.id, Reply.Ok(Bytes(byteArrayOf()))) }, token,
                            Math.addExact(SystemClock.uptimeMillis(), effect.milliseconds.longValueExact()))
                    }
                    is Effect.Read -> {
                        val value = storage.getString(effect.key, null) ?: error("No stored value for this key")
                        answer(command.id, Reply.Ok(Bytes(Base64.decode(value, Base64.NO_WRAP))))
                    }
                    is Effect.Write -> {
                        check(storage.edit().putString(effect.key, Base64.encodeToString(effect.value.array(), Base64.NO_WRAP)).commit()) {
                            "Private storage write failed"
                        }
                        answer(command.id, Reply.Ok(Bytes(byteArrayOf())))
                    }
                    is Effect.Log -> { Log.i("Kotlean", effect.text); answer(command.id, Reply.Ok(Bytes(byteArrayOf()))) }
                    Effect.Haptic -> {
                        check(renderer.content.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK)) { "Haptic feedback unavailable" }
                        answer(command.id, Reply.Ok(Bytes(byteArrayOf())))
                    }
                    is Effect.Clipboard -> {
                        activity.getSystemService(ClipboardManager::class.java).setPrimaryClip(ClipData.newPlainText("", effect.text))
                        answer(command.id, Reply.Ok(Bytes(byteArrayOf())))
                    }
                    is Effect.Platform -> {
                        val plugin = plugins[effect.name] ?: error("Unknown platform plugin: ${effect.name}")
                        plugin.execute(activity, effect.payload.array()) { result ->
                            if (!closed) answer(command.id, result.fold({ Reply.Ok(Bytes(it)) }, ::errorReply))
                        }
                    }
                }
            } catch (error: Exception) { answer(command.id, errorReply(error)) }
        }

        override fun onActivityResumed(owner: Activity) {
            if (owner !== activity || closed) return
            dispatch(Event.Lifecycle(true))
            subscriptions.values.map { it.value }.filter { it.source is Source.Resume }.forEach(::signal)
        }
        override fun onActivityPaused(owner: Activity) {
            if (owner !== activity || closed) return
            dispatch(Event.Lifecycle(false))
            subscriptions.values.map { it.value }.filter { it.source is Source.Pause }.forEach(::signal)
        }
        override fun onActivitySaveInstanceState(owner: Activity, state: Bundle) {
            if (owner !== activity || closed) return
            try {
                val out = Wire.decodeOut(native!!.step(Wire.encodeEvent(Event.Save)))
                check(out is Out.Changes) { "Save did not return an output frame" }
                state.putByteArray(stateKey, out.value.snapshot?.array())
            } catch (error: Exception) { close(); failure(activity, error) }
        }
        override fun onActivityDestroyed(owner: Activity) { if (owner === activity) close() }
        override fun onActivityCreated(owner: Activity, state: Bundle?) = Unit
        override fun onActivityStarted(owner: Activity) = Unit
        override fun onActivityStopped(owner: Activity) = Unit
        override fun onConfigurationChanged(configuration: Configuration) { post(renderer::refreshSizes) }
        @Suppress("OVERRIDE_DEPRECATION")
        override fun onLowMemory() = Unit

        override fun close() {
            if (closed) return
            check(Looper.myLooper() == Looper.getMainLooper()) { "Kotlean close requires the Android main thread" }
            closed = true
            handler.removeCallbacksAndMessages(token)
            queue.clear()
            subscriptions.clear()
            back?.close()
            back = null
            if (lifecycleRegistered) {
                activity.application.unregisterActivityLifecycleCallbacks(this)
                lifecycleRegistered = false
            }
            if (configurationRegistered) {
                activity.application.unregisterComponentCallbacks(this)
                configurationRegistered = false
            }
            activity.window.decorView.setTag(R.id.kotlean_owner, null)
            try { native?.close() } finally {
                native = null
                val owned = Collections.newSetFromMap(IdentityHashMap<PlatformPlugin, Boolean>())
                owned.addAll(plugins.values)
                for (plugin in owned) runCatching { plugin.close() }.onFailure { Log.e("Kotlean", "Plugin close failed", it) }
            }
        }
    }
}
