import KotleanBuild.Runner

open System KotleanBuild

def main (args : List String) : IO Unit := do
  let [toolchain, ndk, runtime, libuv, work, jobsText, patchFile] := args
    | throw (IO.userError "Usage: lean --run tools/BuildRuntime.lean TOOLCHAIN NDK RUNTIME_SOURCE LIBUV_SOURCE WORK JOBS PATCH")
  let some jobs := jobsText.toNat? | throw (IO.userError "JOBS must be positive")
  if jobs == 0 then throw (IO.userError "JOBS must be positive")
  let base ← IO.currentDir
  let toolchain := base / toolchain
  let ndk := base / ndk
  let runtime := base / runtime
  let libuv := base / libuv
  let work := base / work
  let patch := base / patchFile
  let patchedObject := work / "object-full-pointers.cpp"
  let sources ← (runtime / "src/runtime").walkDir
  let sources := sources.filter fun path =>
    path.extension == some "cpp" && path.fileName != some "openssl.cpp"
  if sources.isEmpty then throw (IO.userError "No runtime source files")
  let githash ← Runner.execute (toolchain / "bin/lean").toString #["--githash"]
  IO.FS.writeFile (work / "include/githash.h") s!"#pragma once\n#define LEAN_GITHASH {Lean.Json.str githash.trimAscii.toString |>.compress}\n"
  let compiler := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin/clang++"
  let context := (← Runner.digest (ndk / "source.properties")) ++
    (← Runner.digest compiler) ++ (← Runner.digest (work / "include/lean/config.h")) ++
    (← Runner.digest (work / "include/lean/lean.h")) ++
    (← Runner.digest (work / "include/lean/version.h")) ++
    (← Runner.digest (work / "include/githash.h")) ++
    (← Runner.digest (libuv / "include/uv.h"))
  IO.println s!"Runtime units: {sources.size}; workers: {jobs}"
  (← IO.getStdout).flush
  let lock ← IO.FS.Handle.mk (work / ".runtime.lock") .append
  lock.lock
  try
    let _ ← Runner.execute "patch" #["--batch", "--fuzz=0", "--output=" ++ patchedObject.toString,
      (runtime / "src/runtime/object.cpp").toString, patch.toString]
    Runner.parallel sources jobs fun source => do
      let some suffix := source.toString.dropPrefix? ((runtime / "src/runtime").toString ++ "/")
        | throw (IO.userError "Runtime source outside configured directory")
      let relative : FilePath := suffix.toString
      let compilationSource := if relative.toString == "object.cpp" then patchedObject else source
      let object := FilePath.mk "obj/runtime" / relative.withExtension "o"
      IO.FS.createDirAll ((work / object).parent.getD ".")
      let signature : Signature := ⟨1, context, .androidArm64, "r30-api26", "1.48.0",
        ["-O2", "-fPIC", "-std=c++20", "-DLEAN_MULTI_THREAD", "-ffunction-sections", "-fdata-sections"],
        [⟨relative.toString, ← Runner.digest compilationSource⟩]⟩
      let rebuilt ← Runner.runStage work (work / "receipts/runtime" / relative.withExtension "json")
        signature object.toString "compile" compiler.toString
        #["--target=aarch64-linux-android26", "-O2", "-fPIC", "-std=c++20", "-DLEAN_MULTI_THREAD",
          "-ffunction-sections", "-fdata-sections", "-I" ++ (work / "include").toString,
          "-I" ++ (runtime / "src").toString, "-I" ++ (libuv / "include").toString,
          "-c", compilationSource.toString, "-o", (work / object).toString]
      IO.println s!"runtime/{relative}: compiled={rebuilt}"
      (← IO.getStdout).flush
    IO.println s!"Runtime compilation complete: {sources.size} units"
  finally
    lock.unlock
