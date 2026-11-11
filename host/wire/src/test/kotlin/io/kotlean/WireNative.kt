// no_kotlin: These test calls load and execute the compiled Lean JNI oracle.
package io.kotlean

import java.util.concurrent.Callable
import java.util.concurrent.Executors

internal object WireNative {
    init { System.load(requireNotNull(System.getProperty("kotlean.wire.library"))) }
    external fun matchesEvent(seed: Long, bytes: ByteArray): Boolean
    external fun matchesInit(seed: Long, bytes: ByteArray): Boolean
    external fun output(seed: Long): ByteArray
    external fun acceptsOut(bytes: ByteArray): Boolean
    external fun acceptsEvent(bytes: ByteArray): Boolean
    external fun echo(bytes: ByteArray): ByteArray
}

internal object NativeWire {
    private val executor = Executors.newSingleThreadExecutor()
    private fun <T> call(action: () -> T): T = executor.submit(Callable { action() }).get()
    fun matchesEvent(seed: Long, bytes: ByteArray): Boolean = call { WireNative.matchesEvent(seed, bytes) }
    fun matchesInit(seed: Long, bytes: ByteArray): Boolean = call { WireNative.matchesInit(seed, bytes) }
    fun output(seed: Long): ByteArray = call { WireNative.output(seed) }
    fun acceptsOut(bytes: ByteArray): Boolean = call { WireNative.acceptsOut(bytes) }
    fun acceptsEvent(bytes: ByteArray): Boolean = call { WireNative.acceptsEvent(bytes) }
    fun echo(bytes: ByteArray): ByteArray = call { WireNative.echo(bytes) }
    fun close() { executor.shutdown() }
}
