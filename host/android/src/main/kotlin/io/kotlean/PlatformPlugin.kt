// no_python: Android plugins provide platform I/O with byte-only replies.
package io.kotlean

import android.app.Activity

interface PlatformPlugin : AutoCloseable {
    fun execute(activity: Activity, payload: ByteArray, reply: (Result<ByteArray>) -> Unit)
    override fun close() = Unit
}
