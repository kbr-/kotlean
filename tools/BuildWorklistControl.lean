import KotleanBuild.Runner

open System KotleanBuild

def main (args : List String) : IO Unit := do
  let [project, ndk, runtime, libuv, cache, directory] := args
    | throw (IO.userError "Usage: lean --run tools/BuildWorklistControl.lean PROJECT NDK RUNTIME LIBUV CACHE OUTPUT_DIRECTORY")
  let project : FilePath := project
  let ndk : FilePath := ndk
  let runtime : FilePath := runtime
  let libuv : FilePath := libuv
  let cache : FilePath := cache
  let output : FilePath := directory
  IO.FS.createDirAll output
  let compiler := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin/clang++"
  let mut objects := #[]
  for file in ← (runtime / "src/runtime").walkDir do
    if file.extension == some "cpp" && file.fileName != some "object.cpp" &&
        file.fileName != some "openssl.cpp" then
      let some relative := file.toString.dropPrefix? ((runtime / "src/runtime").toString ++ "/")
        | throw (IO.userError "Runtime source outside configured directory")
      objects := objects.push (cache / "obj/runtime" / FilePath.mk relative.toString |>.withExtension "o")
  for (name, source, original) in [
      ("original", runtime / "src/runtime/object.cpp", true),
      ("full", cache / "object-full-pointers.cpp", false)] do
    let object := output / s!"{name}.o"
    let defines := if original then #["-DKOTLEAN_ORIGINAL_WORKLIST"] else #[]
    let _ ← Runner.execute compiler.toString <| #["--target=aarch64-linux-android26", "-O2", "-fPIC",
      "-std=c++20", "-DLEAN_MULTI_THREAD", "-ffunction-sections", "-fdata-sections",
      "-DKOTLEAN_RUNTIME_OBJECT=\"" ++ source.toString ++ "\"",
      "-I" ++ (cache / "include").toString, "-I" ++ (runtime / "src").toString,
      "-I" ++ (libuv / "include").toString, "-c",
      (project / "host/wire/src/test/cpp/android_worklist.cpp").toString, "-o", object.toString] ++ defines
    let executable := output / name
    let _ ← Runner.execute compiler.toString <| #["--target=aarch64-linux-android26", "-pie",
      "-Wl,--gc-sections", "-Wl,--no-undefined", "-static-libstdc++", "-o", executable.toString,
      object.toString] ++ objects.map FilePath.toString ++ #["-Wl,--start-group",
      (cache / "libstandard.a").toString, (libuv / "build/libuv.a").toString,
      "-Wl,--end-group", "-llog"]
    IO.println s!"Worklist control built: {executable}"
