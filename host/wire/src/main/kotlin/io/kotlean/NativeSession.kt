// no_kotlin: The JVM owns the native reference and exposes the fixed JNI byte transport.
package io.kotlean

/** The caller loads its app library before creating a session, on the session's owning thread. */
class NativeSession(input: ByteArray) : AutoCloseable {
    private var handle: Long = 0
    val initialOutput: ByteArray = start(input)

    private external fun start(input: ByteArray): ByteArray
    external fun step(input: ByteArray): ByteArray
    external override fun close()
}
