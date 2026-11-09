// no_python: Gradle's JVM plugin provides Kotlin compilation and test execution.
plugins { id("org.jetbrains.kotlin.jvm") }

kotlin {
    jvmToolchain(21)
    compilerOptions {
        jvmTarget.set(org.jetbrains.kotlin.gradle.dsl.JvmTarget.JVM_17)
        allWarningsAsErrors.set(true)
        optIn.add("io.kotest.common.ExperimentalKotest")
    }
}

dependencies {
    testImplementation("io.kotest:kotest-runner-junit5:6.2.6")
    testImplementation("io.kotest:kotest-property:6.2.6")
}

tasks.test {
    useJUnitPlatform()
    maxParallelForks = 1
    systemProperty("kotlean.wire.library", providers.gradleProperty("wireLibrary").getOrElse(""))
    testLogging { exceptionFormat = org.gradle.api.tasks.testing.logging.TestExceptionFormat.FULL }
}
