// no_python: Gradle requires a Kotlin DSL settings entry point.
pluginManagement { repositories { google(); mavenCentral(); gradlePluginPortal() } }
dependencyResolutionManagement { repositories { google(); mavenCentral() } }
rootProject.name = "kotlean"
include(":wire")
project(":wire").projectDir = file("host/wire")
