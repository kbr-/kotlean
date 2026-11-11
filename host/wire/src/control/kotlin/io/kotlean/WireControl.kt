// no_kotlin: This JVM property control uses the cached Kotlin compiler and real JNI oracle.
package io.kotlean

import java.util.Random

private fun acceptsPacket(bytes: ByteArray): Boolean = try {
    Wire.decodeOut(bytes)
    true
} catch (_: WireException) {
    false
}

fun main() {
    try {
        check(NativeWire.acceptsOut(NativeWire.output(0))) { "native positive control" }
        check(!NativeWire.acceptsOut(byteArrayOf(-1, 0))) { "native negative control" }
        for (size in listOf(0, 128, 8192, 65536)) {
            println("Checking native text event: $size ASCII bytes")
            val value = Event.Node(java.math.BigInteger.ZERO, java.math.BigInteger.ZERO,
                Input.Text("x".repeat(size)))
            val bytes = Wire.encodeEvent(value)
            check(NativeWire.acceptsEvent(bytes)) { "large event size=$size" }
            check(!NativeWire.acceptsEvent(bytes + byteArrayOf(0))) { "large trailing event size=$size" }
        }
        val longCount = byteArrayOf(0) + ByteArray(65536) { 128.toByte() }
        println("Checking native long frame counts")
        check(!NativeWire.acceptsEvent(longCount)) { "unterminated frame count" }
        check(!NativeWire.acceptsEvent(longCount + byteArrayOf(1))) { "oversized frame count" }
        val grammar = listOf(
            intArrayOf(), intArrayOf(255, 0), intArrayOf(1, 2, 0, 0),
            intArrayOf(1, 129, 0, 0), intArrayOf(2, 3, 2, 192, 128),
            intArrayOf(2, 4, 3, 237, 160, 128), intArrayOf(2, 5, 4, 244, 144, 128, 128),
            intArrayOf(0, 15, 0, 1, 1, 8, 0, 2, 5, 128, 128, 128, 128, 16, 0, 0, 0),
            intArrayOf(0, 11, 0, 1, 1, 4, 0, 9, 1, 2, 0, 0, 0),
            intArrayOf(0, 5, 0, 0, 0, 0, 2), intArrayOf(1, 1, 2)
        ).map { values -> ByteArray(values.size) { values[it].toByte() } }
        for ((index, packet) in grammar.withIndex()) {
            check(!NativeWire.acceptsOut(packet)) { "invalid native grammar control $index" }
            check(!acceptsPacket(packet)) { "grammar index=$index" }
        }
        val random = Random(113)
        val seeds = (0L..255L).toList() + listOf(Long.MIN_VALUE, Long.MAX_VALUE, -1L) +
            List(256) { random.nextLong() }
        for (seed in seeds) {
            check(NativeWire.matchesEvent(seed, Wire.encodeEvent(Fixture.event(seed)))) { "event seed=$seed" }
            check(NativeWire.matchesInit(seed, Wire.encodeInit(Fixture.initial(seed)))) { "init seed=$seed" }
            val valid = NativeWire.output(seed)
            check(Wire.decodeOut(valid) == Fixture.output(seed)) { "output seed=$seed" }
            val raw = ByteArray(random.nextInt(257)).also { random.nextBytes(it) }
            val original = raw.copyOf()
            check(NativeWire.echo(raw).contentEquals(original)) { "transport seed=$seed" }
            check(raw.contentEquals(original)) { "input mutation seed=$seed" }
            val mutated = valid.copyOf()
            val at = java.lang.Long.remainderUnsigned(seed, mutated.size.toLong()).toInt()
            mutated[at] = (mutated[at].toInt() xor 128).toByte()
            for (packet in listOf(raw, valid, mutated, valid + byteArrayOf(0))) {
                check(acceptsPacket(packet) == NativeWire.acceptsOut(packet)) { "acceptance seed=$seed" }
            }
        }
        println("JVM wire semantic/acceptance/transport control passed: ${seeds.size} seed samples")
    } finally {
        NativeWire.close()
    }
}
