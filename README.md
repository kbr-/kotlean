# Kotlean: Android apps, proven

**The code you prove is the code that runs.**

Write an Android app's model, updates, views and effect descriptions in Lean. Compile that Lean to
native code and run it behind a small Kotlin host.

Kotlean is in development. The interface below is the target API:

```kotlin
Kotlean.run(this, "counter", savedInstanceState)
```

Implemented: Lean codecs for platform events, view patches, drawing, commands, subscription changes
and optional snapshot bytes. They carry prefix round-trip, canonical-prefix and positive-length
proofs. Complete-frame decoding accepts exactly canonical encodings and rejects trailing bytes. The
Android host and examples are still in development.

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

Build the Lean package with the pinned toolchain:

```sh
cd lean
lake build
```

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

Development targets: Lean 4.34.0, Android Native Development Kit (NDK) r30, Android API 26 or later,
compile Software Development Kit (SDK) 37.

Planned examples:

- **Counter:** the single-call host with buttons, persistence and a delayed command.
- **SnackNet:** an artificial intelligence (AI) maze-chase game. Collect tokens, evade human
  operators and pick up **Overclock** to reverse the chase.

Licensed under the [MIT License](LICENSE).
