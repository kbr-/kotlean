// no_python: Gradle's plugin-development APIs require a JVM build definition.
plugins {
    id("java-gradle-plugin")
}

java { toolchain.languageVersion.set(JavaLanguageVersion.of(21)) }
tasks.withType<JavaCompile>().configureEach {
    options.release.set(17)
    options.compilerArgs.addAll(listOf("-Xlint:all", "-Werror"))
}
dependencies { compileOnly("com.android.tools.build:gradle-api:9.5.1") }

gradlePlugin {
    plugins {
        create("kotlean") {
            id = "io.kotlean"
            implementationClass = "io.kotlean.gradle.KotleanPlugin"
        }
    }
}
