# Kotlean: Android apps, proven

**The code you prove is the code that runs.**

Write an Android app's model, updates, views and effect descriptions in Lean. Compile that Lean to
native code and run it behind a small Kotlin host.

Call the host from `Activity.onCreate` after `super.onCreate`.

```kotlin
Kotlean.run(this, "counter", savedInstanceState)
```

Lean codecs cover platform events, view patches, drawing, commands, subscription changes and
optional snapshot bytes. They carry prefix round-trip, canonical-prefix and positive-length proofs.
Complete-frame decoding accepts exactly canonical encodings and rejects trailing bytes. The Android
host applies the patches to native Views and gives the Activity ownership of the session.

The Java Virtual Machine (JVM) protocol binding is tested against compiled Lean through the Java
Native Interface (JNI). A control using existing cached artifacts checks complete semantic fixtures,
malformed input and byte transport; targeted mutations check that faults are detected. The full
Gradle test build also passes through the real JNI library.

The natural-number routines and list decoder use accumulator loops proved equivalent to their
reference definitions. Native controls include 64 KiB text and long malformed frame counts.

The Lean property diff is proved to produce the new record while avoiding unchanged setters,
duplicate updates and reordered fields.

The primitive scene interpreter has proofs for record creation, property changes, child moves,
removal and root selection. The scene diff generator has proofs that unchanged scenes emit nothing
and ids with unchanged kinds are never removed or recreated. Unchanged structure permits property
setters only. For valid old and new scenes, applying the diff is proved to return the new scene.

Scene diff endpoints use dense zero-based preorder ids: walking the root and its ordered children
visits 0 through the node count minus one. A nonempty scene has root 0, each nonroot has one parent,
scroll has at most one child, and leaves have none; an empty scene has no root.

Typed Lean views support column, row, text, button, input, scroll and canvas, with handlers kept
outside the rendered scene. Compilation is proved to produce canonical preorder scenes and matching
handler registries; changing only handler closures preserves the rendered scene.

The pure Lean app runtime has proofs for current-view dispatch, one-shot continuations, subscription
reconciliation, suspension of ticks while inactive, save/restore and controlled text edits. Accepted
edits on surviving inputs emit no text setter. See the [runtime
laws](lean/Kotlean/Runtime/Laws.lean) and [proofs](lean/Kotlean/Runtime/Verified.lean).

The [native byte adapter](lean/Kotlean/Native.lean) proves initialization and event agreement,
malformed-input behavior and terminal absent state. A compile-time exporter and generic JNI session
keep app-specific model and message types in Lean. JVM controls run both numeric and text models
through updates, saving, restoration and closing. Linux ownership controls compare repeated starts,
updates and frees with deliberately retained states.

The Lean build executable resolves an app package through Lake and cross-compiles its generated C
for Android arm64/API 26. It generates Init and Std with the pinned compiler, checks authored
objects for libc replacements and reuses a complete standard-library archive after checking its
inputs and bytes. A physical Android device has passed the text-model JNI control. The Android
runtime [patch](native/android/object-full-pointers.patch) keeps full pointers in the deletion
worklist so heap pointer tags survive deallocation. Lean's runtime retains its [Apache 2.0
license](native/android/LEAN-LICENSE.txt).

Build the Lean package with the pinned toolchain:

```sh
cd lean
lake build
```

Build the examples from the repository root with JDK 21, Gradle 9.9 and Android SDK 37. Run
`lake build kotlean` in `lean/` and point `KOTLEAN_BUILD` to the resulting executable in
`lean/.lake/build/bin/`. Set `KOTLEAN_TOOLCHAIN` to the installed Lean toolchain,
`KOTLEAN_LEAN_SOURCE` to its matching source checkout, `ANDROID_NDK_HOME` to NDK r30,
`KOTLEAN_LIBUV_SOURCE` to the Android arm64 libuv build tree, and `KOTLEAN_CACHE` to a writable
native build cache. The libuv tree must contain `build/libuv.a`. Set `ANDROID_HOME` to the SDK.

```sh
gradle --no-daemon :counter:assembleDebug :snacknet:assembleDebug
```

The `io.kotlean` Gradle plugin discovers Lean inputs and packages the generated native library. The
APK is at `examples/counter/build/outputs/apk/debug/counter-debug.apk`. The counter keeps its count
and note in Lean, requests a delayed increment and persists the result in private storage.
SnackNet's APK is at `examples/snacknet/build/outputs/apk/debug/snacknet-debug.apk`.

The arm64 native library extracted from each release APK is stripped. The table reports the
generated library, the extracted release library and a separate gzip measurement of that release
library.

| Example | Generated bytes | Stripped bytes | Stripped + gzip bytes |
| --- | ---: | ---: | ---: |
| Counter | 6,846,272 | 1,694,760 | 534,745 |
| SnackNet | 7,756,040 | 2,178,360 | 667,508 |

The design uses `init`, `update`, `view` and `subscriptions`. App-specific models and messages stay
in Lean. A fixed byte protocol carries platform events in and view patches, commands and
subscription changes out. Android Views render the result.

The verification contract covers codec round trips, view diff correctness, event dispatch and
one-shot command continuations with Lean theorems. The Java Native Interface (JNI), the Kotlin
renderer and Android behavior require integration and device tests. An app's author proves its own
update properties.

The first version runs Lean on the Android main thread. Keep `update` and `view` within the frame
budget: about 16 ms at 60 Hz. Keep saved-instance state small because Android shares its Binder
transaction buffer across the process's transactions.

Android tick subscriptions deliver the current uptime in milliseconds as eight little-endian
bytes. Animation can use the elapsed time between ticks, independently of callback timing.

Development targets: Lean 4.34.0, Android Native Development Kit (NDK) r30, Android API 26 or later,
compile Software Development Kit (SDK) 37.

SnackNet is a maze-chase game with an AI machine pursued by human operators. Steer by swiping,
rolling a thumb across the D-pad or using directional keys. The machine moves continuously
between cells and queues a turn until the next junction where it can take it. One operator tracks the machine and
the other aims ahead of it. Both periodically patrol and keep moving through corridors. Collect
all thirteen data tokens in the 15-by-13 maze to open the exit. Pick up **Overclock** to transform
the machine into a metal endoskeleton and reverse the chase. The Lean rules prove that a successful step reaches a
neighboring traversable cell, tokens never increase during a run and a powered tick preserves
the player's lives.

A complete Pixel 11 Pro playthrough finished with 130 points and three lives. Android reported
917 rendered frames and zero janky frames after reset. The final 114 consecutive presentation
timestamps ran at 60.05 frames per second with a maximum interval of 16.68 ms. For foreground
device testing, build the debug variant with `-PsnacknetDeviceTest=true`. The flag is off in
default debug and release builds.

Licensed under the [MIT License](LICENSE).
