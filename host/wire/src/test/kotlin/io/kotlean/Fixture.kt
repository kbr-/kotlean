// no_kotlin: Expected JVM values are constructed independently of the wire codec.
package io.kotlean

import java.math.BigInteger

internal object Fixture {
    private val two64 = BigInteger.ONE.shiftLeft(64)
    private val two32 = BigInteger.ONE.shiftLeft(32)
    private operator fun BigInteger.plus(value: Int): BigInteger = add(BigInteger.valueOf(value.toLong()))
    private operator fun BigInteger.times(value: Int): BigInteger = multiply(BigInteger.valueOf(value.toLong()))
    private operator fun BigInteger.div(value: Int): BigInteger = divide(BigInteger.valueOf(value.toLong()))
    private fun BigInteger.index(value: Int): Int = mod(BigInteger.valueOf(value.toLong())).toInt()
    private fun number(seed: Long): BigInteger = BigInteger(java.lang.Long.toUnsignedString(seed))
    private fun payload(n: BigInteger): Bytes = Bytes(ByteArray(n.index(5)) { (n + it * 7).toByte() })
    private fun label(n: BigInteger): String = "λ🤖/$n"
    private fun point(n: BigInteger): Point = Point(n, (n + 1).negate())
    private fun flag(n: BigInteger, bit: Int): Boolean = n.testBit(bit)
    private fun color(n: BigInteger): Long = n.mod(two32).toLong()

    private fun kind(n: BigInteger): NodeKind = when (n.index(7)) {
        0 -> NodeKind.COLUMN; 1 -> NodeKind.ROW; 2 -> NodeKind.TEXT; 3 -> NodeKind.BUTTON
        4 -> NodeKind.INPUT; 5 -> NodeKind.SCROLL; else -> NodeKind.CANVAS
    }
    private fun phase(n: BigInteger): TouchPhase = when (n.index(4)) {
        0 -> TouchPhase.DOWN; 1 -> TouchPhase.MOVE; 2 -> TouchPhase.UP; else -> TouchPhase.CANCEL
    }
    private fun dimension(n: BigInteger): Dimension = when (n.index(3)) {
        0 -> Dimension.Wrap; 1 -> Dimension.Fill; else -> Dimension.Dp(n + 2)
    }
    private fun alignment(n: BigInteger): Alignment = when (n.index(3)) {
        0 -> Alignment.START; 1 -> Alignment.CENTER; else -> Alignment.FINISH
    }
    private fun source(n: BigInteger): Source = when (n.index(5)) {
        0 -> Source.Tick(n + 1); 1 -> Source.Back; 2 -> Source.Pause; 3 -> Source.Resume
        else -> Source.Platform(label(n), payload(n))
    }
    private fun mask(n: BigInteger): ListenerMask =
        ListenerMask(flag(n, 0), flag(n, 1), flag(n, 2), flag(n, 3), flag(n, 4))

    private fun drawing(n: BigInteger): List<Draw> = listOf(
        Draw.Clear(color(n)),
        Draw.Rect(point(n), n + 2, n + 3, n + 4, color(n + 5)),
        Draw.Circle(point(n + 1), n + 6, color(n + 7)),
        Draw.Line(point(n), point(n + 1), n + 8, color(n + 9)),
        Draw.Polygon(List(n.index(4)) { point(n + it) }, color(n + 10)),
        Draw.Text(point(n + 2), n + 11, label(n), color(n + 12), alignment(n + 13), n + 14)
    )

    private fun property(n: BigInteger): Property = when (n.index(14)) {
        0 -> Property.Text(label(n)); 1 -> Property.Hint(label(n + 1))
        2 -> Property.Foreground(color(n)); 3 -> Property.Background(color(n + 1))
        4 -> Property.Width(dimension(n)); 5 -> Property.Height(dimension(n + 1))
        6 -> Property.Padding(n + 2); 7 -> Property.Weight(n + 3); 8 -> Property.TextSize(n + 4)
        9 -> Property.Enabled(flag(n, 0)); 10 -> Property.Description(label(n))
        11 -> Property.Align(alignment(n)); 12 -> Property.Drawing(drawing(n))
        else -> Property.Listeners(mask(n))
    }

    private fun input(n: BigInteger): Input = when (n.index(5)) {
        0 -> Input.Click
        1 -> Input.Text(label(n))
        2 -> Input.Touch(TouchFrame(phase(n), BigInteger.valueOf(n.index(3).toLong()), n + two64,
            List(n.index(4)) { Contact(n + it * 7, point(n + it)) }))
        3 -> Input.Key(n + two64, flag(n, 0))
        else -> Input.Resize(n + 1, n + 2, n + 3)
    }

    fun event(seed: Long): Event {
        val n = number(seed)
        return when (n.index(5)) {
            0 -> Event.Node(n + two64, n + 17, input(n / 5))
            1 -> Event.Answer(n + 19, if (flag(n / 5, 0)) Reply.Error(label(n)) else Reply.Ok(payload(n)))
            2 -> Event.Subscription(n * 7 + 1, n * 11 + 2, payload(n))
            3 -> Event.Lifecycle(flag(n, 0))
            else -> Event.Save
        }
    }

    private fun effects(n: BigInteger): List<Effect> = listOf(
        Effect.Delay(n + 1), Effect.Read(label(n)), Effect.Write(label(n + 1), payload(n)),
        Effect.Log(label(n + 2)), Effect.Haptic, Effect.Clipboard(label(n + 3)),
        Effect.Platform(label(n + 4), payload(n + 1))
    )

    fun output(seed: Long): Out {
        val n = number(seed)
        return when (n.index(3)) {
            0 -> Out.Changes(Output(n + two64,
                listOf(Patch.Create(n, kind(n)), Patch.SetProperty(n, property(n / 3)),
                    Patch.SetProperty(n, Property.Drawing(drawing(n))),
                    Patch.SetProperty(n, Property.Listeners(mask(n))),
                    Patch.Insert(n, n + 1, n + 2), Patch.Remove(n + 3),
                    Patch.Root(if (flag(n, 0)) n else null)),
                effects(n).mapIndexed { i, effect -> Command(n + 100 + i, effect) },
                listOf(SubscriptionChange.Add(Subscription(n + 11, n + 13, source(n))),
                    SubscriptionChange.Remove(n + 11, n + 12)),
                if (flag(n, 2)) payload(n) else null))
            1 -> Out.Ignored(if (flag(n, 1)) label(n) else null)
            else -> Out.Failed(label(n))
        }
    }

    fun initial(seed: Long): Bytes? {
        val n = number(seed)
        return if (flag(n, 0)) payload(n) else null
    }
}
