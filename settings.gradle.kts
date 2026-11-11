// no_kotlin: Gradle requires a Kotlin DSL settings entry point.
pluginManagement {
    includeBuild("gradle-plugin")
    repositories { google(); mavenCentral() }
}
dependencyResolutionManagement { repositories { google(); mavenCentral() } }
rootProject.name = "kotlean"
include(":wire")
project(":wire").projectDir = file("host/wire")
include(":android")
project(":android").projectDir = file("host/android")
include(":counter")
project(":counter").projectDir = file("examples/counter")
include(":snacknet")
project(":snacknet").projectDir = file("examples/snacknet")
