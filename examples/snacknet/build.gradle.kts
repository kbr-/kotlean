// no_python: Android packaging uses the Kotlean Gradle plugin.
plugins {
    id("com.android.application")
    id("io.kotlean")
}

android {
    namespace = "io.kotlean.snacknet"
    compileSdk = 37
    ndkVersion = "30.0.16248370"
    ndkPath = providers.environmentVariable("ANDROID_NDK_HOME").orNull
    defaultConfig {
        applicationId = "io.kotlean.snacknet"
        minSdk = 26
        targetSdk = 37
        versionCode = 1
        versionName = "1.0"
    }
}

dependencies { implementation(project(":android")) }
