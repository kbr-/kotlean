// no_python: This JVM control exercises a failing generated module initializer through JNI.
package io.kotlean

fun main(args: Array<String>) {
    require(args.size == 1)
    try {
        System.load(args[0])
        error("A failed module initializer was accepted")
    } catch (error: UnsatisfiedLinkError) {
        check(error.message.orEmpty().lowercase().contains("unsupported jni version 0xffffffff")) { error.toString() }
        println("Failed module initializer refused by JNI")
    }
}
