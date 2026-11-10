// no_python: The Android Gradle plugin builds the fixed platform adapter.
plugins { id("com.android.library") }

android {
    namespace = "io.kotlean"
    compileSdk = 37
    defaultConfig { minSdk = 26 }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    sourceSets.getByName("main").kotlin.directories.add("../wire/src/main/kotlin")
}
