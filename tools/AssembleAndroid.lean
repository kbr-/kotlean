import KotleanBuild.Runner

open System KotleanBuild

def main (args : List String) : IO Unit := do
  let [project, _toolchain, ndk, runtime, libuv, work, source, initializer, output] := args
    | throw (IO.userError "Usage: lean --run tools/AssembleAndroid.lean PROJECT TOOLCHAIN NDK RUNTIME_SOURCE LIBUV_SOURCE WORK SOURCES_JSON INITIALIZER OUTPUT")
  let base ← IO.currentDir
  let project := base / project
  let ndk := base / ndk
  let runtime := base / runtime
  let libuv := base / libuv
  let work := base / work
  let source := base / source
  let output := base / output
  let bin := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin"
  let clang := bin / "clang"
  let clangpp := bin / "clang++"
  let .ok paths := Lean.Json.parse (← IO.FS.readFile source) >>= Lean.fromJson? (α := Array String)
    | throw (IO.userError "Invalid generated-C source list")
  let packageSources := paths.map FilePath.mk
  let headers ← Runner.androidLeanHeaders clang work
  let mut packageObjects := #[]
  for file in packageSources do
    let cDigest ← Runner.digest file
    let relative : FilePath := cDigest
    let object := FilePath.mk "obj/package" / relative.withExtension "o"
    IO.FS.createDirAll ((work / object).parent.getD ".")
    let signature : Signature := ⟨1, "4.34.0", .androidArm64, headers, "", ["-O2", "-fPIC"],
      [⟨file.toString, cDigest⟩]⟩
    let _ ← Runner.runStage work (work / "receipts/package" / relative.withExtension "json") signature
      object.toString "compile" clang.toString #["--target=aarch64-linux-android26", "-O2", "-fPIC",
        "-ffunction-sections", "-fdata-sections", "-I" ++ (work / "include").toString,
        "-c", file.toString, "-o", (work / object).toString]
    packageObjects := packageObjects.push (work / object)
  let _ ← Runner.execute clangpp.toString #["--target=aarch64-linux-android26", "-O2", "-fPIC",
    "-std=c++17", "-fno-exceptions", "-fno-rtti", "-DKOTLEAN_INITIALIZER=" ++ initializer,
    "-I" ++ (work / "include").toString, "-I" ++ (project / "native/include").toString,
    "-c", (project / "native/app_jni.cpp").toString, "-o", (work / "app_jni.o").toString]
  let mut objects := #[work / "app_jni.o"] ++ packageObjects
  for file in ← (runtime / "src/runtime").walkDir do
    if file.extension == some "cpp" && file.fileName != some "openssl.cpp" then
      let some relative := file.toString.dropPrefix? ((runtime / "src/runtime").toString ++ "/")
        | throw (IO.userError "Runtime C outside its source root")
      objects := objects.push (work / "obj/runtime" / FilePath.mk relative.toString |>.withExtension "o")
  for object in objects do
    unless ← object.pathExists do throw (IO.userError s!"Missing support object: {object}")
  IO.FS.createDirAll (output.parent.getD ".")
  let temporary := output.toString ++ ".tmp"
  let _ ← Runner.execute clangpp.toString <| #["--target=aarch64-linux-android26", "-shared",
    "-Wl,--gc-sections", "-Wl,--no-undefined", "-Wl,--version-script=" ++ (project / "native/exports.map").toString,
    "-static-libstdc++", "-o", temporary] ++ objects.map FilePath.toString ++
    #["-Wl,--start-group", (work / "libstandard.a").toString,
      (libuv / "build/libuv.a").toString, "-Wl,--end-group", "-llog"]
  let own ← Runner.execute (bin / "llvm-nm").toString <|
    #["-j", "--defined-only"] ++ objects.map FilePath.toString ++
      #[(work / "libstandard.a").toString, (libuv / "build/libuv.a").toString]
  let libc ← Runner.execute (bin / "llvm-nm").toString #["-D", "-j", "--defined-only",
    (ndk / "toolchains/llvm/prebuilt/linux-x86_64/sysroot/usr/lib/aarch64-linux-android/26/libc.so").toString]
  let ownNames := own.splitOn "\n" |>.filter (· != "")
  let libcNames := libc.splitOn "\n" |>.filter (· != "") |>.map (fun name => (name.splitOn "@").head!)
  unless libcNames.contains "free" && libcNames.contains "malloc" do
    throw (IO.userError "The libc symbol counterpart omitted known functions")
  let conflicts := clashes ownNames libcNames
  unless conflicts.isEmpty do throw (IO.userError s!"Native library defines libc symbols: {conflicts}")
  IO.FS.rename temporary output
  IO.println s!"Android library linked: {output}; objects: {objects.size}; no libc symbol clashes"
