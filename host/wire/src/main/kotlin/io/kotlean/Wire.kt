// no_kotlin: Kotlin binds the fixed byte protocol to Android and JVM consumers.
package io.kotlean

import java.io.ByteArrayOutputStream
import java.math.BigInteger
import java.nio.ByteBuffer
import java.nio.CharBuffer
import java.nio.charset.CharacterCodingException
import java.nio.charset.CodingErrorAction
import java.nio.charset.StandardCharsets

internal class WireException(message: String) : IllegalArgumentException(message)

internal object Wire {
    private val zero = BigInteger.ZERO
    private val one = BigInteger.ONE
    private val lowSeven = BigInteger.valueOf(127)

    private class Writer {
        private val output = ByteArrayOutputStream()
        fun finish(): ByteArray = output.toByteArray()
        fun byte(value: Int) { output.write(value) }
        fun natural(value: BigInteger) {
            if (value.signum() < 0) throw WireException("Negative natural field")
            var rest = value
            do {
                val digit = rest.and(lowSeven).toInt()
                rest = rest.shiftRight(7)
                byte(digit or if (rest.signum() == 0) 0 else 128)
            } while (rest.signum() != 0)
        }
        fun signed(value: BigInteger) {
            natural(if (value.signum() < 0) value.negate().shiftLeft(1).subtract(one) else value.shiftLeft(1))
        }
        fun boolean(value: Boolean) { byte(if (value) 1 else 0) }
        fun bytes(value: ByteArray) {
            natural(BigInteger.valueOf(value.size.toLong()))
            output.write(value)
        }
        fun text(value: String) {
            try {
                val buffer = StandardCharsets.UTF_8.newEncoder()
                    .onMalformedInput(CodingErrorAction.REPORT).onUnmappableCharacter(CodingErrorAction.REPORT)
                    .encode(CharBuffer.wrap(value))
                val encoded = ByteArray(buffer.remaining())
                buffer.get(encoded)
                bytes(encoded)
            } catch (_: CharacterCodingException) {
                throw WireException("Invalid UTF-16 platform text")
            }
        }
        fun frame(tag: Int, body: Writer.() -> Unit) {
            val payload = Writer().apply(body).finish()
            byte(tag)
            bytes(payload)
        }
        fun <T> optional(value: T?, body: Writer.(T) -> Unit) {
            if (value == null) byte(0) else { byte(1); body(value) }
        }
        fun <T> list(values: List<T>, body: Writer.(T) -> Unit) {
            natural(BigInteger.valueOf(values.size.toLong()))
            for (value in values) body(value)
        }
    }

    private class Reader(private val bytes: ByteArray, private var position: Int = 0, private val limit: Int = bytes.size) {
        fun end() { if (position != limit) throw WireException("Trailing protocol bytes") }
        fun byte(): Int {
            if (position == limit) throw WireException("Truncated protocol field")
            return bytes[position++].toInt() and 255
        }
        fun natural(): BigInteger {
            var value = zero
            var shift = 0
            while (true) {
                val raw = byte()
                val digit = raw and 127
                value = value.or(BigInteger.valueOf(digit.toLong()).shiftLeft(shift))
                if (raw and 128 == 0) {
                    if (shift != 0 && digit == 0) throw WireException("Noncanonical natural field")
                    return value
                }
                if (shift > Int.MAX_VALUE - 7) throw WireException("Natural field exceeds JVM capacity")
                shift += 7
            }
        }
        fun signed(): BigInteger {
            val value = natural()
            val high = value.shiftRight(1)
            return if (value.testBit(0)) high.negate().subtract(one) else high
        }
        fun boolean(): Boolean = when (byte()) {
            0 -> false; 1 -> true; else -> throw WireException("Invalid Boolean tag")
        }
        private fun count(): Int {
            val count = natural()
            if (count > BigInteger.valueOf((limit - position).toLong())) throw WireException("Truncated list or payload")
            return count.toInt()
        }
        fun bytes(): ByteArray {
            val size = count()
            val result = bytes.copyOfRange(position, position + size)
            position += size
            return result
        }
        fun text(): String = try {
            StandardCharsets.UTF_8.newDecoder().onMalformedInput(CodingErrorAction.REPORT)
                .onUnmappableCharacter(CodingErrorAction.REPORT).decode(ByteBuffer.wrap(bytes())).toString()
        } catch (_: CharacterCodingException) {
            throw WireException("Invalid UTF-8 protocol text")
        }
        fun color(): Long {
            val value = natural()
            if (value.bitLength() > 32) throw WireException("Color exceeds unsigned 32-bit range")
            return value.toLong()
        }
        fun <T> optional(body: Reader.() -> T): T? = when (byte()) {
            0 -> null; 1 -> body(); else -> throw WireException("Invalid optional tag")
        }
        fun <T> list(body: Reader.() -> T): List<T> = List(count()) { body() }
        fun <T> frame(body: Reader.(Int) -> T): T {
            val tag = byte()
            val size = count()
            val payload = Reader(bytes, position, position + size)
            position += size
            val result = payload.body(tag)
            payload.end()
            return result
        }
    }

    private fun unknown(tag: Int): Nothing = throw WireException("Unknown protocol tag $tag")
    private fun Writer.point(value: Point) { signed(value.x); signed(value.y) }
    private fun Writer.phase(value: TouchPhase) {
        frame(when (value) { TouchPhase.DOWN -> 0; TouchPhase.MOVE -> 1; TouchPhase.UP -> 2; TouchPhase.CANCEL -> 3 }) {}
    }
    private fun Writer.touch(value: TouchFrame) {
        phase(value.phase); natural(value.changed); natural(value.milliseconds)
        list(value.contacts) { natural(it.id); point(it.point) }
    }
    private fun Writer.input(value: Input) {
        when (value) {
            Input.Click -> frame(0) {}
            is Input.Text -> frame(1) { text(value.value) }
            is Input.Touch -> frame(2) { touch(value.value) }
            is Input.Key -> frame(3) { natural(value.code); boolean(value.down) }
            is Input.Resize -> frame(4) { natural(value.width); natural(value.height); natural(value.density) }
        }
    }
    private fun Writer.reply(value: Reply) {
        when (value) {
            is Reply.Ok -> frame(0) { bytes(value.value.array()) }
            is Reply.Error -> frame(1) { text(value.message) }
        }
    }
    fun encodeEvent(value: Event): ByteArray = Writer().apply {
        when (value) {
            is Event.Node -> frame(0) { natural(value.revision); natural(value.id); input(value.input) }
            is Event.Answer -> frame(1) { natural(value.id); reply(value.reply) }
            is Event.Subscription -> frame(2) { natural(value.generation); natural(value.id); bytes(value.payload.array()) }
            is Event.Lifecycle -> frame(3) { boolean(value.active) }
            Event.Save -> frame(4) {}
        }
    }.finish()
    fun encodeInit(snapshot: Bytes?): ByteArray = Writer().apply { optional(snapshot) { bytes(it.array()) } }.finish()

    private fun Reader.point(): Point = Point(signed(), signed())
    private fun Reader.kind(): NodeKind = frame { tag -> when (tag) {
        0 -> NodeKind.COLUMN; 1 -> NodeKind.ROW; 2 -> NodeKind.TEXT; 3 -> NodeKind.BUTTON
        4 -> NodeKind.INPUT; 5 -> NodeKind.SCROLL; 6 -> NodeKind.CANVAS; else -> unknown(tag)
    } }
    private fun Reader.source(): Source = frame { tag -> when (tag) {
        0 -> Source.Tick(natural()); 1 -> Source.Back; 2 -> Source.Pause; 3 -> Source.Resume
        4 -> Source.Platform(text(), Bytes(bytes())); else -> unknown(tag)
    } }
    private fun Reader.effect(): Effect = frame { tag -> when (tag) {
        0 -> Effect.Delay(natural()); 1 -> Effect.Read(text()); 2 -> Effect.Write(text(), Bytes(bytes()))
        3 -> Effect.Log(text()); 4 -> Effect.Haptic; 5 -> Effect.Clipboard(text())
        6 -> Effect.Platform(text(), Bytes(bytes())); else -> unknown(tag)
    } }
    private fun Reader.command(): Command = Command(natural(), effect())
    private fun Reader.subscription(): Subscription = Subscription(natural(), natural(), source())
    private fun Reader.dimension(): Dimension = frame { tag -> when (tag) {
        0 -> Dimension.Wrap; 1 -> Dimension.Fill; 2 -> Dimension.Dp(natural()); else -> unknown(tag)
    } }
    private fun Reader.alignment(): Alignment = frame { tag -> when (tag) {
        0 -> Alignment.START; 1 -> Alignment.CENTER; 2 -> Alignment.FINISH; else -> unknown(tag)
    } }
    private fun Reader.draw(): Draw = frame { tag -> when (tag) {
        0 -> Draw.Clear(color())
        1 -> Draw.Rect(point(), natural(), natural(), natural(), color())
        2 -> Draw.Circle(point(), natural(), color())
        3 -> Draw.Line(point(), point(), natural(), color())
        4 -> Draw.Polygon(list { point() }, color())
        5 -> Draw.Text(point(), natural(), text(), color())
        else -> unknown(tag)
    } }
    private fun Reader.mask(): ListenerMask = ListenerMask(boolean(), boolean(), boolean(), boolean(), boolean())
    private fun Reader.property(): Property = frame { tag -> when (tag) {
        0 -> Property.Text(text()); 1 -> Property.Hint(text()); 2 -> Property.Foreground(color())
        3 -> Property.Background(color()); 4 -> Property.Width(dimension()); 5 -> Property.Height(dimension())
        6 -> Property.Padding(natural()); 7 -> Property.Weight(natural()); 8 -> Property.TextSize(natural())
        9 -> Property.Enabled(boolean()); 10 -> Property.Description(text()); 11 -> Property.Align(alignment())
        12 -> Property.Drawing(list { draw() }); 13 -> Property.Listeners(mask()); else -> unknown(tag)
    } }
    private fun Reader.patch(): Patch = frame { tag -> when (tag) {
        0 -> Patch.Create(natural(), kind()); 1 -> Patch.SetProperty(natural(), property())
        2 -> Patch.Insert(natural(), natural(), natural()); 3 -> Patch.Remove(natural())
        4 -> Patch.Root(optional { natural() }); else -> unknown(tag)
    } }
    private fun Reader.change(): SubscriptionChange = frame { tag -> when (tag) {
        0 -> SubscriptionChange.Add(subscription())
        1 -> SubscriptionChange.Remove(natural(), natural()); else -> unknown(tag)
    } }
    private fun Reader.output(): Output = Output(natural(), list { patch() }, list { command() },
        list { change() }, optional { Bytes(bytes()) })
    private fun Reader.out(): Out = frame { tag -> when (tag) {
        0 -> Out.Changes(output()); 1 -> Out.Ignored(optional { text() }); 2 -> Out.Failed(text()); else -> unknown(tag)
    } }
    fun decodeOut(bytes: ByteArray): Out {
        val reader = Reader(bytes)
        val result = reader.out()
        reader.end()
        return result
    }
}
