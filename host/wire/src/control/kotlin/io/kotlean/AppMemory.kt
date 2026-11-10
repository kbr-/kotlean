// no_python: This JVM control measures the real JNI application's native allocation lifetime.
package io.kotlean

import java.math.BigInteger

internal object AppAllocator {
    external fun stats(): String
    external fun retain(session: NativeSession)
    external fun references(session: NativeSession): String
    external fun trackModel(session: NativeSession)
    external fun releaseModel(): Int
}

fun main(args: Array<String>) {
    require(args.size in 2..4 && args[1] in listOf("normal", "leak"))
    System.load(args[0])
    val value = "m".repeat(8192)
    val event = Wire.encodeEvent(Event.Node(BigInteger.ZERO, BigInteger.ZERO, Input.Text(value)))
    val initial = Wire.encodeInit(null)
    val warmup = args.getOrNull(2)?.toInt() ?: 1000
    val cycles = args.getOrNull(3)?.toInt() ?: 5000
    val control = NativeSession(initial)
    println("INITIAL REFS ${AppAllocator.references(control)}")
    control.step(event)
    println("STEPPED REFS ${AppAllocator.references(control)}")
    val snapshot = (Wire.decodeOut(control.step(Wire.encodeEvent(Event.Save))) as Out.Changes).value.snapshot
    AppAllocator.trackModel(control)
    control.close()
    val remaining = AppAllocator.releaseModel()
    println("MODEL REFS AFTER CLOSE $remaining")
    check(remaining == 1) { "Closing the session retained $remaining model references, including the probe" }
    println("CLOSED REFS ${AppAllocator.references(control)}")
    val restored = NativeSession(Wire.encodeInit(snapshot))
    println("RESTORED REFS ${AppAllocator.references(restored)}")
    AppAllocator.trackModel(restored)
    restored.close()
    val restoredRemaining = AppAllocator.releaseModel()
    println("RESTORED MODEL REFS AFTER CLOSE $restoredRemaining")
    check(restoredRemaining == 1) { "Closing the restored session retained $restoredRemaining model references, including the probe" }
    fun cycle() {
        val session = NativeSession(initial)
        check(Wire.decodeOut(session.step(event)) is Out.Changes)
        if (args[1] == "leak") AppAllocator.retain(session)
        session.close()
    }
    repeat(warmup) { cycle() }
    println("ALLOCATOR WARM ${args[1]}\n${AppAllocator.stats()}")
    repeat(2) { phase ->
        repeat(cycles) { cycle() }
        println("ALLOCATOR PHASE ${phase + 1} ${args[1]}\n${AppAllocator.stats()}")
    }
}
