// no_kotlin: Android packaging uses the Kotlean Gradle plugin.
plugins {
    id("com.android.application")
    id("io.kotlean")
}

android {
    namespace = "io.kotlean.counter"
    compileSdk = 37
    ndkVersion = "30.0.16248370"
    ndkPath = providers.environmentVariable("ANDROID_NDK_HOME").orNull
    defaultConfig {
        applicationId = "io.kotlean.counter"
        minSdk = 36
        targetSdk = 37
        versionCode = 1
        versionName = "1.0"
    }
}

dependencies { implementation(project(":android")) }
