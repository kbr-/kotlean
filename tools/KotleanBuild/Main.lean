import Lake.CLI.Main
import Lean.Compiler.NameMangling
import KotleanBuild.Runner
import KotleanBuild.Verified

open System KotleanBuild

def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name | throw (IO.userError s!"Set {name} to the installed dependency directory")
  return value

def main (args : List String) : IO Unit := do
  let ["build", package, moduleText, output] := args
    | throw (IO.userError "Usage: kotlean build PACKAGE MODULE|auto OUTPUT")
  let base ← IO.currentDir
  let package := base / package
  let output := base / output
  let toolchain := base / (← requiredEnv "KOTLEAN_TOOLCHAIN")
  let ndk := base / (← requiredEnv "ANDROID_NDK_HOME")
  let runtime := base / (← requiredEnv "KOTLEAN_LEAN_SOURCE")
  let libuv := base / (← requiredEnv "KOTLEAN_LIBUV_SOURCE")
  let cache ← requiredEnv "KOTLEAN_CACHE"
  let work := base / cache
  let lean ← Lake.LeanInstall.get toolchain
  let .ok environment ← (Lake.Env.compute (Lake.LakeInstall.ofLean lean) lean none).toBaseIO
    | throw (IO.userError "Cannot load the pinned Lake environment")
  let some workspace ← (Lake.loadWorkspace {lakeEnv := environment, wsDir := package}).toBaseIO
    | throw (IO.userError "Cannot resolve the Lean package")
  let moduleName ← if moduleText == "auto" then do
    let some target := workspace.root.defaultTargets[0]?
      | throw (IO.userError "The package needs a default Lean library target, or an explicit module")
    pure target
  else pure moduleText.toName
  let some app := workspace.findModule? moduleName
    | throw (IO.userError s!"Unknown app module: {moduleName}")
  let some sdk := workspace.findModule? `Kotlean
    | throw (IO.userError "The app package must require Kotlean")
  let project := sdk.pkg.dir.parent.getD sdk.pkg.dir
  let bin := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin"
  let prerequisites := [toolchain / "bin/lean", toolchain / "bin/lake", ndk / "source.properties",
    bin / "clang", bin / "clang++", bin / "llvm-nm", bin / "llvm-ar", toolchain / "include/lean/version.h",
    toolchain / "src/lean/Init.lean", toolchain / "src/lean/Std.lean",
    runtime / "src/runtime/object.cpp", libuv / "build/libuv.a", app.leanFile,
    project / "native/android/lean/config.h", project / "native/android/object-full-pointers.patch",
    project / "native/exports.map", project / "native/app_jni.cpp"]
  let mut missing := []
  for file in prerequisites do
    unless ← file.pathExists do missing := missing ++ [file.toString]
  for command in ["cmake", "patch"] do
    try
      let result ← IO.Process.output {cmd := command, args := #["--version"]}
      if result.exitCode != 0 then missing := missing ++ [command]
    catch _ => missing := missing ++ [command]
  let .ok _ := preflight missing ["package", "standard", "runtime", "link"]
    | throw (IO.userError s!"Missing prerequisite: {missing.head!}")
  IO.FS.createDirAll work
  let cacheLock ← IO.FS.Handle.mk (work / ".build.lock") .append
  cacheLock.lock
  try
    IO.FS.createDirAll (work / "include/lean")
    let _ ← Runner.execute "cmake" #["-E", "copy_directory", (runtime / "src/include/lean").toString,
      (work / "include/lean").toString]
    let _ ← Runner.execute "cmake" #["-E", "copy_if_different", (toolchain / "include/lean/version.h").toString,
      (work / "include/lean/version.h").toString]
    let _ ← Runner.execute "cmake" #["-E", "copy_if_different", (project / "native/android/lean/config.h").toString,
      (work / "include/lean/config.h").toString]
    let previous ← IO.currentDir
    let mut modules := #[moduleName.toString]
    IO.Process.setCurrentDir package
    try
      let _ ← Runner.execute (toolchain / "bin/lake").toString #["build"]
      let data ← Runner.execute (toolchain / "bin/lake").toString #["--json", "query", s!"+{moduleName}:transImports"]
      let .ok imports := Lean.Json.parse data.trimAscii.toString >>= Lean.fromJson? (α := Array String)
        | throw (IO.userError "Lake returned an invalid module-dependency result")
      modules := modules ++ imports
      let _ ← Runner.execute (toolchain / "bin/lake").toString <|
        #["build"] ++ modules.map (fun name => s!"+{name}:c")
    finally
      IO.Process.setCurrentDir previous
    let mut sources : Array String := #[]
    for name in modules do
      let some module := workspace.findModule? name.toName
        | throw (IO.userError s!"Lake module disappeared: {name}")
      sources := sources.push module.cFile.toString
    let sourceList := work / "package-sources.json"
    IO.FS.writeFile sourceList (Lean.toJson sources |>.compress)
    let initializer := Lean.mkModuleInitializationFunctionName app.name app.pkg.id? .runtime
    let libraryPath := project / "lean/.lake/build/lib/lean"
    let run := fun script arguments => do
      let result ← IO.Process.output {
        cmd := (toolchain / "bin/lean").toString
        args := #["-j12", "--run", (project / "tools" / script).toString] ++ arguments
        env := #[("LEAN_PATH", some libraryPath.toString)]
      }
      IO.print result.stdout
      IO.eprint result.stderr
      if result.exitCode != 0 then throw (IO.userError s!"{script} failed ({result.exitCode})")
    run "GenerateStandard.lean" #[toolchain.toString, ndk.toString, work.toString, "12", "all"]
    run "BuildRuntime.lean" #[toolchain.toString, ndk.toString, runtime.toString, libuv.toString,
      work.toString, "12", (project / "native/android/object-full-pointers.patch").toString]
    run "AssembleAndroid.lean" #[project.toString, toolchain.toString, ndk.toString, runtime.toString,
      libuv.toString, work.toString, sourceList.toString, initializer, output.toString]
    IO.println s!"Kotlean Android build complete: {output}"
  finally
    cacheLock.unlock
