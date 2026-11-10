// no_python: Kotest samples the real JVM codec and native Lean/JNI implementation.
package io.kotlean

import io.kotest.core.spec.style.StringSpec
import io.kotest.matchers.shouldBe
import io.kotest.property.Arb
import io.kotest.property.PropTestConfig
import io.kotest.property.arbitrary.byte
import io.kotest.property.arbitrary.list
import io.kotest.property.arbitrary.long
import io.kotest.property.arbitrary.int
import io.kotest.property.checkAll

private val config = PropTestConfig(seed = 113L, iterations = 256)
private val boundaries = (0L..255L).toList() + listOf(Long.MIN_VALUE, Long.MAX_VALUE, -1L)

private fun accepts(bytes: ByteArray): Boolean = try {
    Wire.decodeOut(bytes)
    true
} catch (_: WireException) {
    false
}

class WirePropertyTest : StringSpec({
    afterSpec { NativeWire.close() }

    "native oracle has real positive and negative controls" {
        NativeWire.acceptsOut(NativeWire.output(0)) shouldBe true
        NativeWire.acceptsOut(byteArrayOf(-1, 0)) shouldBe false
        NativeWire.matchesEvent(4, byteArrayOf(4, 0)) shouldBe true
        NativeWire.matchesEvent(0, byteArrayOf(4, 0)) shouldBe false
        NativeWire.matchesInit(0, byteArrayOf(0)) shouldBe true
        NativeWire.matchesInit(0, byteArrayOf(2)) shouldBe false
    }

    "eventMatchesLeanFixture" {
        for (seed in boundaries) NativeWire.matchesEvent(seed, Wire.encodeEvent(Fixture.event(seed))) shouldBe true
        checkAll(config, Arb.long()) { seed ->
            NativeWire.matchesEvent(seed, Wire.encodeEvent(Fixture.event(seed))) shouldBe true
        }
    }

    "initMatchesLeanFixture" {
        for (seed in boundaries) NativeWire.matchesInit(seed, Wire.encodeInit(Fixture.initial(seed))) shouldBe true
        checkAll(config, Arb.long()) { seed ->
            NativeWire.matchesInit(seed, Wire.encodeInit(Fixture.initial(seed))) shouldBe true
        }
    }

    "largeTextEventsAreAcceptedWithoutTrailingBytes" {
        fun checkSize(size: Int) {
            val value = Event.Node(java.math.BigInteger.ZERO, java.math.BigInteger.ZERO,
                Input.Text("x".repeat(size)))
            val bytes = Wire.encodeEvent(value)
            NativeWire.acceptsEvent(bytes) shouldBe true
            NativeWire.acceptsEvent(bytes + byteArrayOf(0)) shouldBe false
        }
        for (size in listOf(0, 128, 8192, 65536)) checkSize(size)
        checkAll(PropTestConfig(seed = 113L, iterations = 16), Arb.int(0..65536)) { checkSize(it) }
    }

    "unterminatedLongFrameCountIsRejected" {
        NativeWire.acceptsEvent(byteArrayOf(4, 0)) shouldBe true
        NativeWire.acceptsEvent(byteArrayOf(0) + ByteArray(65536) { 128.toByte() }) shouldBe false
    }

    "oversizedLongFrameCountIsRejected" {
        NativeWire.acceptsEvent(byteArrayOf(4, 0)) shouldBe true
        NativeWire.acceptsEvent(byteArrayOf(0) + ByteArray(65536) { 128.toByte() } + byteArrayOf(1)) shouldBe false
    }

    "outputMatchesLeanFixture" {
        for (seed in boundaries) Wire.decodeOut(NativeWire.output(seed)) shouldBe Fixture.output(seed)
        checkAll(config, Arb.long()) { seed ->
            Wire.decodeOut(NativeWire.output(seed)) shouldBe Fixture.output(seed)
        }
    }

    "outputAcceptanceMatchesLean" {
        checkAll(config, Arb.long(), Arb.list(Arb.byte(), 0..256)) { seed, raw ->
            val valid = NativeWire.output(seed)
            val mutated = valid.copyOf()
            val index = java.lang.Long.remainderUnsigned(seed, mutated.size.toLong()).toInt()
            mutated[index] = (mutated[index].toInt() xor 128).toByte()
            for (bytes in listOf(raw.toByteArray(), valid, mutated, valid + byteArrayOf(0))) {
                accepts(bytes) shouldBe NativeWire.acceptsOut(bytes)
            }
        }
    }

    "jniPreservesBytes" {
        checkAll(config, Arb.list(Arb.byte(), 0..256)) { values ->
            val input = values.toByteArray()
            val original = input.copyOf()
            NativeWire.echo(input).contentEquals(original) shouldBe true
            input.contentEquals(original) shouldBe true
        }
    }
})
