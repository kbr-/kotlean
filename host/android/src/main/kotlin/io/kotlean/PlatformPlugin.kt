// no_python: Android plugins provide platform I/O with byte-only replies.
package io.kotlean

import android.app.Activity

/** Performs platform I/O. Send changes for the Lean-managed view through [reply][execute]. */
interface PlatformPlugin : AutoCloseable {
    fun execute(activity: Activity, payload: ByteArray, reply: (Result<ByteArray>) -> Unit)
    override fun close() = Unit
}
