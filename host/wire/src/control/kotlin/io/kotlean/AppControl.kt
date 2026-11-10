// no_python: This JVM control exercises opaque app state through production JNI.
package io.kotlean

import java.math.BigInteger
import kotlin.random.Random

private fun changes(bytes: ByteArray): Output = (Wire.decodeOut(bytes) as Out.Changes).value

fun main(args: Array<String>) {
    require(args.size == 2) { "Expected native library path and nat|text" }
    System.load(args[0])
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
