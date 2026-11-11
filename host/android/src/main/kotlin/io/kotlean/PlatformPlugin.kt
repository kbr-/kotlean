// no_kotlin: Android plugins provide platform I/O with byte-only replies.
package io.kotlean

import android.app.Activity

/**
 * Performs platform I/O. Send changes for the Lean-managed view through [reply][execute].
 *
 * A plugin serving a platform subscription starts its stream in [subscribe] and stops it when the
 * returned handle closes. [emit] may run on any thread; the host delivers each payload on the main
 * thread while the subscription stays installed, and the runtime ignores a payload for a
 * subscription it no longer holds.
 */
interface PlatformPlugin : AutoCloseable {
    fun execute(activity: Activity, payload: ByteArray, reply: (Result<ByteArray>) -> Unit)
    fun subscribe(activity: Activity, payload: ByteArray, emit: (ByteArray) -> Unit): AutoCloseable =
        throw UnsupportedOperationException("This plugin offers no platform subscription")
    override fun close() = Unit
}
