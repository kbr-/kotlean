// no_kotlin: Gradle's JVM plugin provides Kotlin compilation and test execution.
plugins { id("org.jetbrains.kotlin.jvm") }

kotlin {
    jvmToolchain(21)
    compilerOptions {
        jvmTarget.set(org.jetbrains.kotlin.gradle.dsl.JvmTarget.JVM_17)
        allWarningsAsErrors.set(true)
    }
}

dependencies {
    testImplementation("io.kotest:kotest-runner-junit5:6.2.6")
    testImplementation("io.kotest:kotest-property:6.2.6")
}

tasks.withType<JavaCompile>().configureEach { options.release.set(17) }

tasks.named<org.jetbrains.kotlin.gradle.tasks.KotlinCompile>("compileTestKotlin") {
    compilerOptions.optIn.add("io.kotest.common.ExperimentalKotest")
}

tasks.test {
    val wireLibrary = providers.gradleProperty("wireLibrary")
    inputs.file(wireLibrary).withPropertyName("wireLibrary")
    useJUnitPlatform()
    maxParallelForks = 1
    systemProperty("kotlean.wire.library", wireLibrary.getOrElse(""))
    testLogging { exceptionFormat = org.gradle.api.tasks.testing.logging.TestExceptionFormat.FULL }
}

tasks.register<JavaExec>("appAcceptance") {
    dependsOn(tasks.testClasses)
    classpath = sourceSets.test.get().runtimeClasspath
    mainClass.set("io.kotlean.AppControlKt")
    val appLibrary = providers.gradleProperty("appLibrary")
    val appKind = providers.gradleProperty("appKind")
    doFirst { args(appLibrary.get(), appKind.get()) }
}

tasks.register<JavaExec>("appMemory") {
    dependsOn(tasks.testClasses)
    classpath = sourceSets.test.get().runtimeClasspath
    mainClass.set("io.kotlean.AppMemoryKt")
    maxHeapSize = "64m"
    minHeapSize = "64m"
    val appLibrary = providers.gradleProperty("appLibrary")
    val memoryMode = providers.gradleProperty("memoryMode")
    doFirst { args(appLibrary.get(), memoryMode.get()) }
}

kotlin.sourceSets.test { kotlin.srcDir("src/control/kotlin") }
