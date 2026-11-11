// no_python: This JVM control exercises opaque app state through production JNI.
package io.kotlean

import java.math.BigInteger
import kotlin.random.Random

private fun changes(bytes: ByteArray): Output = (Wire.decodeOut(bytes) as Out.Changes).value

private fun counterControl() {
    val openStart = System.nanoTime()
    val session = NativeSession(Wire.encodeInit(null))
    val openNs = System.nanoTime() - openStart
    session.use {
        var current = changes(session.initialOutput)
        val read = current.commands.single()
        check(read.effect == Effect.Read("counter"))
        fun send(event: Event): Output = changes(session.step(Wire.encodeEvent(event))).also { current = it }
        fun click(id: Long): Output = send(Event.Node(current.revision, BigInteger.valueOf(id), Input.Click))
        fun hasCount(output: Output, count: String): Boolean =
            output.patches.contains(Patch.SetProperty(BigInteger.valueOf(3), Property.Text(count)))
        send(Event.Answer(read.id, Reply.Error("empty storage")))
        val delay = click(7).commands.single()
        check(delay.effect == Effect.Delay(BigInteger.valueOf(500)))
        val unknown = Event.Answer(delay.id + BigInteger.ONE, Reply.Ok(Bytes(byteArrayOf())))
        check(Wire.decodeOut(session.step(Wire.encodeEvent(unknown))) == Out.Ignored(null))
        val answer = Event.Answer(delay.id, Reply.Ok(Bytes(byteArrayOf())))
        val incremented = send(answer)
        check(hasCount(incremented, "1"))
        val stored = (incremented.commands.single().effect as Effect.Write).value
        check(Wire.decodeOut(session.step(Wire.encodeEvent(answer))) == Out.Ignored(null))
        check(hasCount(click(5), "0"))
        check(hasCount(click(6), "1"))
        check(hasCount(click(8), "0"))
        NativeSession(Wire.encodeInit(stored)).use { restored ->
            check(hasCount(changes(restored.initialOutput), "1"))
        }
        NativeSession(Wire.encodeInit(null)).use { disk ->
            val diskRead = changes(disk.initialOutput).commands.single()
            check(hasCount(changes(disk.step(Wire.encodeEvent(Event.Answer(diskRead.id, Reply.Ok(stored))))), "1"))
        }
        NativeSession(Wire.encodeInit(Bytes(byteArrayOf(-128)))).use { invalid ->
            check(hasCount(changes(invalid.initialOutput), "0"))
        }
        val samples = LongArray(1000)
        repeat(1100) { i ->
            val packet = Wire.encodeEvent(Event.Node(current.revision, BigInteger.valueOf(6), Input.Click))
            val before = System.nanoTime()
            val response = session.step(packet)
            val elapsed = System.nanoTime() - before
            current = changes(response)
            check(hasCount(current, (i + 1).toString()))
            if (i >= 100) samples[i - 100] = elapsed
        }
        samples.sort()
        println("Counter JNI timing ns: session_open=$openNs step_p50=${samples[499]} step_p95=${samples[949]} samples=${samples.size}")
    }
    session.close()
    check(Wire.decodeOut(session.step(Wire.encodeEvent(Event.Save))) == Out.Ignored(null))
    println("Counter JNI control passed: request IDs, duplicate answer, storage bytes, snapshot, invalid snapshot and repeated close")
}

fun main(args: Array<String>) {
    require(args.size == 2) { "Expected native library path and nat|text|counter" }
    System.load(args[0])
    if (args[1] == "counter") {
        counterControl()
        return
    }
    val random = Random(715091)
    val nat = args[1] == "nat"
    require(nat || args[1] == "text")
    val zero = BigInteger.ZERO
    val one = BigInteger.ONE
    repeat(128) { trial ->
        val session = NativeSession(Wire.encodeInit(null))
        val initial = changes(session.initialOutput)
        check(initial.revision == zero && initial.commands.isEmpty() && initial.subscriptions.isEmpty())
        check(initial.patches.contains(Patch.SetProperty(zero, Property.Text(if (nat) "7" else "ready"))))
        var revision = zero
        var count = BigInteger.valueOf(7)
        var text = "ready"
        repeat(24) { event ->
            val input = if (nat) Input.Click else Input.Text("$trial:$event:${random.nextLong()}:λ🙂")
            val incoming = Wire.encodeEvent(Event.Node(revision, zero, input))
            val original = incoming.copyOf()
            val output = changes(session.step(incoming))
            check(original.contentEquals(incoming))
            revision += one
            if (nat) count += one else text = (input as Input.Text).value
            val patches = if (nat) listOf(Patch.SetProperty(zero, Property.Text(count.toString()))) else emptyList()
            check(output == Output(revision, patches, emptyList(), emptyList(), null))
            check(Wire.decodeOut(session.step(byteArrayOf())) == Out.Ignored("Malformed event packet"))
            check(Wire.decodeOut(session.step(Wire.encodeEvent(Event.Node(revision + one, zero, input)))) == Out.Ignored(null))
        }
        val snapshot = changes(session.step(Wire.encodeEvent(Event.Save))).snapshot
        check(snapshot != null)
        val restored = NativeSession(Wire.encodeInit(snapshot))
        val restoredOutput = changes(restored.initialOutput)
        check(restoredOutput.patches.contains(Patch.SetProperty(zero, Property.Text(if (nat) count.toString() else text))))
        restored.close()
        session.close()
        session.close()
        check(Wire.decodeOut(session.step(Wire.encodeEvent(Event.Save))) == Out.Ignored(null))
        check(Wire.decodeOut(session.step(byteArrayOf())) == Out.Ignored(null))
        session.close()
    }
    val invalid = NativeSession(byteArrayOf())
    check(Wire.decodeOut(invalid.initialOutput) == Out.Failed("Malformed initialization packet"))
    check(Wire.decodeOut(invalid.step(Wire.encodeEvent(Event.Save))) == Out.Ignored(null))
    invalid.close()
    val fallback = NativeSession(Wire.encodeInit(Bytes(byteArrayOf(-128))))
    check(changes(fallback.initialOutput).patches.contains(Patch.SetProperty(zero, Property.Text(if (nat) "7" else "ready"))))
    var wrongThread: Throwable? = null
    val thread = Thread { try { fallback.step(Wire.encodeEvent(Event.Save)) } catch (error: Throwable) { wrongThread = error } }
    thread.isDaemon = true
    thread.start()
    thread.join(1000)
    check(!thread.isAlive) { "Wrong-thread rejection did not return" }
    check(wrongThread is IllegalStateException)
    fallback.close()
    println("Opaque ${args[1]} app: generated event streams, restoration, malformed packets, repeated close, terminal events and thread ownership passed")
}
