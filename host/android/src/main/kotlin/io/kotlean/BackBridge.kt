// no_python: Android exposes distinct legacy and modern back callback APIs.
package io.kotlean

import android.annotation.TargetApi
import android.app.Activity
import android.os.Build
import android.view.KeyEvent
import android.view.Window
import android.window.OnBackInvokedCallback
import android.window.OnBackInvokedDispatcher

internal class BackBridge(private val activity: Activity, private val send: (Subscription) -> Unit) : AutoCloseable {
    private var subscriptions: List<Subscription> = emptyList()
    private var modern: AutoCloseable? = null
    private val previous = activity.window.callback
    private val callback = object : Window.Callback by previous {
        override fun dispatchKeyEvent(event: KeyEvent): Boolean {
            if (event.keyCode == KeyEvent.KEYCODE_BACK && subscriptions.isNotEmpty()) {
                if (event.action == KeyEvent.ACTION_UP && !event.isCanceled) subscriptions.toList().forEach(send)
                return true
            }
            return previous.dispatchKeyEvent(event)
        }
    }

    init { activity.window.callback = callback }

    fun update(values: List<Subscription>) {
        if (values == subscriptions) return
        subscriptions = values
        modern?.close()
        modern = null
        if (Build.VERSION.SDK_INT >= 33 && values.isNotEmpty()) {
            val registered = values.toList()
            modern = Modern.register(activity) { registered.forEach(send) }
        }
    }

    override fun close() {
        subscriptions = emptyList()
        modern?.close()
        modern = null
        if (activity.window.callback === callback) activity.window.callback = previous
    }

    @TargetApi(33)
    private object Modern {
        fun register(activity: Activity, action: () -> Unit): AutoCloseable {
            val callback = OnBackInvokedCallback(action)
            activity.onBackInvokedDispatcher.registerOnBackInvokedCallback(OnBackInvokedDispatcher.PRIORITY_DEFAULT, callback)
            return AutoCloseable { activity.onBackInvokedDispatcher.unregisterOnBackInvokedCallback(callback) }
        }
    }
}
