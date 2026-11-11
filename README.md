# Kotlean: Android apps, proven

**The code you prove is the code that runs.**

Kotlean lets you write an Android app's state, behavior and UI in Lean, prove properties of that
code, and compile it into the app. A small Kotlin host renders native Android Views and performs
platform effects.

The problem it addresses is keeping a verified state machine connected to the application people
actually use. Your Lean `update` and `view` functions run on the device. Buttons, text edits,
gestures and timers enter that same state machine.

## See it running

<div align="center">

https://github.com/user-attachments/assets/448f86d3-7b9e-4f29-8ada-afcb71112eef

</div>

SnackNet is an original maze-chase game written in Lean. An AI machine collects thirteen data tokens
while two human operators track and intercept it. **Overclock** turns the machine into a metal
endoskeleton and lets it capture the operators. The recording shows a full win, including the
continuously held D-pad and its highlighted directions.

The game has a 15-by-13 maze, continuous motion, buffered turns, swipe and keyboard steering, pause
and restart. Its rules and drawing live in
[SnackNet.Game](examples/snacknet/lean/SnackNet/Game.lean) and
[SnackNet.View](examples/snacknet/lean/SnackNet/View.lean).

The [Counter example](examples/counter) is a smaller starter with buttons, an editable note, a
delayed increment, private-storage persistence and saved-instance restoration.

## What you can build

- Native interfaces with columns, rows, text, buttons, editable inputs and scrolling.
- Canvas interfaces and games with drawing commands, multitouch and keyboard input.
- Stateful apps with timers, Back handling, lifecycle subscriptions and persistence.
- Android integrations through named plugins with byte payloads and replies.

App-specific models and messages stay in Lean. Both examples use the same Kotlin interface.

## Architecture

The architecture follows an Elm-style model/update/view loop and Roc's separation between
application logic and platform effects. [Elm
architecture](https://guide.elm-lang.org/architecture/buttons) · [Roc
platforms](https://www.roc-lang.org/docs/main/langref/platforms/)

1. `init` creates the model and initial commands.
2. `update` consumes a message and returns a new model and command descriptions.
3. `view` describes the native widgets or Canvas drawing.
4. `subscriptions` describes the events the app currently wants.
5. The host performs effects and sends their replies back through the Lean runtime.

```text
Android input → Event bytes → Lean update → Lean view/diff → Out bytes
      ↑                                                       ↓
      └──────── effect replies and subscriptions ← Android host
```

Lean computes the view patches, request IDs and subscription changes. A fixed byte protocol crosses
JNI. The Kotlin host interprets patches using Android Views and Canvas. One generated Lean app
library runs per process; Activities using that library have separate sessions.

The first version runs Lean on Android's main thread. Keep updates and drawing within the device's
frame budget. Tick subscriptions carry eight little-endian bytes containing uptime in milliseconds,
so animation can use elapsed time between callbacks.

## Write an app

Counter is a complete starter with a Lake package, Gradle configuration, manifest and Activity. A
minimal Lean app has this shape.

```lean
module
import Kotlean
meta import Kotlean.Export

open Kotlean

inductive Msg where
  | increment

def update (_ : Msg) (count : Nat) : Nat × List (Cmd Msg) :=
  (count + 1, [])

theorem increment_adds_one (count : Nat) :
    (update .increment count).1 = count + 1 := rfl

def app : App := {
  Model := Nat
  Msg := Msg
  init := (0, [])
  update := update
  view := fun count => .column { padding := 16 }
    [ .text { text := toString count, textSize := 28 }
    , .button { text := "+1", events := { click := some .increment } } ]
}

kotlean_app app
```

`kotlean_app` generates the native entry points at compile time. Start the host from
`Activity.onCreate` after `super.onCreate`.

```kotlin
Kotlean.run(this, "counter", savedInstanceState)
```

The host owns the session through Activity destruction. Apps can supply a persistence codec, and
command replies return through one-shot Lean continuations.

The Gradle plugin defaults to the app's `lean/` Lake package, its default target, and the Gradle
project name as the native library name. You can set them explicitly.

```kotlin
kotlean {
    packageDirectory.set(file("lean"))
    module.set("Counter")
    libraryName.set("counter")
}
```

See the repository [settings](settings.gradle.kts), [Counter
build](examples/counter/build.gradle.kts) and [Lake package](examples/counter/lean/lakefile.toml)
for complete wiring.

## Build the examples

Use Linux x86-64 with Lean **4.34.0**, JDK **21**, Gradle **9.9**, Android SDK **37**, NDK **r30**,
CMake, Git and `patch`. The apps require **Android 16 or later, API 36+**, on arm64.

From the repository root, configure the installed tools and local build directories.

```sh
export ANDROID_HOME=/path/to/Android/Sdk
export ANDROID_NDK_HOME=/path/to/android-ndk-r30
export KOTLEAN_TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.34.0"
export KOTLEAN_LEAN_SOURCE="$PWD/.deps/lean4"
export KOTLEAN_LIBUV_SOURCE="$PWD/.deps/libuv"
export KOTLEAN_CACHE="$PWD/.cache/kotlean"

mkdir -p .deps
git clone --depth 1 --branch v4.34.0 https://github.com/leanprover/lean4 "$KOTLEAN_LEAN_SOURCE"
git clone --depth 1 --branch v1.48.0 https://github.com/libuv/libuv "$KOTLEAN_LIBUV_SOURCE"

cmake -S "$KOTLEAN_LIBUV_SOURCE" -B "$KOTLEAN_LIBUV_SOURCE/build" \
  -DCMAKE_TOOLCHAIN_FILE="$ANDROID_NDK_HOME/build/cmake/android.toolchain.cmake" \
  -DANDROID_ABI=arm64-v8a -DANDROID_PLATFORM=android-26 \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
  -DCMAKE_C_FLAGS="-ffunction-sections -fdata-sections" \
  -DBUILD_TESTING=OFF -DLIBUV_BUILD_TESTS=OFF -DLIBUV_BUILD_SHARED=OFF
cmake --build "$KOTLEAN_LIBUV_SOURCE/build" --target uv_a

lake -d lean build kotlean
export KOTLEAN_BUILD="$PWD/lean/.lake/build/bin/kotlean"
gradle --no-daemon :counter:assembleDebug :snacknet:assembleDebug
```

The APKs are written to `examples/counter/build/outputs/apk/debug/counter-debug.apk` and
`examples/snacknet/build/outputs/apk/debug/snacknet-debug.apk`.

The build generates Init and Std C with the pinned compiler, compiles Lean's runtime and links the
selected app. Runtime imports support Init, Std and workspace modules compiled from Lean. Use
`meta import` for Lean frontend and Lake code. Platform I/O goes through plugins. The NDK API 26
compilation target is compatible with the app's API 36 minimum.

The included runtime [patch](native/android/object-full-pointers.patch) preserves full pointer words
in Lean's deletion worklist. Content-based receipts support incremental builds.

For device development, `-PsnacknetDeviceTest=true` enables a debug-only foreground mode that keeps
the display on and lets SnackNet appear over the lock screen. Default debug and release builds leave
it off.

## Verification boundary

Kotlean has Lean proofs for its wire codecs, canonical UI compilation, scene diff correctness, event
dispatch, one-shot command continuations and subscription reconciliation. The [runtime
laws](lean/Kotlean/Runtime/Laws.lean) and [proofs](lean/Kotlean/Runtime/Verified.lean) expose those
contracts.

App authors prove their update properties. SnackNet proves traversable neighboring moves,
non-increasing token counts and preservation of lives during powered contact.

JNI, Kotlin rendering and Android behavior are checked through integration and device tests. The
compiler and Android platform remain in the trusted execution path. Keep saved-instance data small
because Android shares the process's Binder transaction buffer.

## Measurements

A Pixel 11 Pro playthrough reached the exit with **130 points and three lives**. Android reported
**917 rendered frames and zero janky frames** after reset. The final 114 valid presentation
timestamps averaged **60.05 FPS**, with a maximum interval of **16.68 ms**.

For Counter, 1,000 warmed native JNI increment steps measured **39.25 μs median** and **47.29 μs
p95**. That interval covers the native step with pre-encoded input. Two cold Activity launches
reported **174 ms** and **140 ms**.

The table compares generated arm64 native libraries with their stripped copies extracted from
release APKs. The gzip column is a separate compression measurement.

| Example | Generated bytes | Stripped bytes | Stripped + gzip bytes |
| --- | ---: | ---: | ---: |
| Counter | 6,846,184 | 1,694,760 | 535,719 |
| SnackNet | 7,866,504 | 2,264,960 | 700,126 |

## License

Kotlean is [MIT licensed](LICENSE). Lean's runtime retains its [Apache 2.0
license](native/android/LEAN-LICENSE.txt).
