import Lake.CLI.Main
import Lean.Compiler.NameMangling
import KotleanBuild.Runner
import KotleanBuild.Verified

open System KotleanBuild

def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name | throw (IO.userError s!"Set {name} to the installed dependency directory")
  return value

def runtimeModules (workspace : Lake.Workspace) (app : Lake.Module) : IO (Array Lake.Module) := do
  let mut modules := #[app]
  let mut seen : Std.HashSet Lean.Name := ({} : Std.HashSet Lean.Name).insert app.name
  let mut cursor := 0
  while cursor < modules.size do
    let some module := modules[cursor]? | break
    cursor := cursor + 1
    let header ← Lean.parseImports' (← IO.FS.readFile module.leanFile) module.leanFile.toString
    for imp in header.imports do
      if imp.isMeta || seen.contains imp.module then continue
      seen := seen.insert imp.module
      if let some dependency := workspace.findModule? imp.module then
        modules := modules.push dependency
  return modules

def main (args : List String) : IO Unit := do
  let (operation, package, moduleText, output) ← match args with
    | ["build", package, moduleText, output] => pure ("build", package, moduleText, output)
    | ["inputs", package, moduleText] => pure ("inputs", package, moduleText, "")
    | _ => throw (IO.userError "Usage: kotlean build PACKAGE MODULE|auto OUTPUT; kotlean inputs PACKAGE MODULE|auto")
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
  let project := sdk.pkg.dir
  let bin := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin"
  let prerequisites := [toolchain / "bin/lean", toolchain / "bin/lake", ndk / "source.properties",
    bin / "clang", bin / "clang++", bin / "ld.lld", bin / "llvm-nm", bin / "llvm-ar",
    toolchain / "include/lean/version.h",
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
  if operation == "inputs" then
    let emit := fun (file : FilePath) => IO.print (file.toString ++ "\u0000")
    let emitDirectory := fun (directory : FilePath) => do
      for file in ← directory.walkDir do
        unless (← file.isDir) do emit file
    let previous ← IO.currentDir
    let data ← try
      IO.Process.setCurrentDir package
      Runner.execute (toolchain / "bin/lake").toString #["--json", "query", s!"+{moduleName}:transImports"]
    finally
      IO.Process.setCurrentDir previous
    let .ok imports := Lean.Json.parse data.trimAscii.toString >>= Lean.fromJson? (α := Array String)
      | throw (IO.userError "Lake returned an invalid module-dependency result")
    for name in #[moduleName.toString] ++ imports do
      let some module := workspace.findModule? name.toName
        | throw (IO.userError s!"Lake module disappeared: {name}")
      emit module.leanFile
    for pkg in workspace.packages do
      for name in ["lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"] do
        let path := pkg.dir / name
        if ← path.pathExists then emit path
    for file in prerequisites do emit file
    emit (← IO.appPath)
    emit (toolchain / "lib/lean/libleanshared.so")
    for directory in [project / "native", project / "tools", runtime / "src",
        libuv / "include", toolchain / "src/lean/Init", toolchain / "src/lean/Std",
        project / ".lake/build/lib/lean/KotleanBuild"] do
      emitDirectory directory
    for directory in ← Runner.androidHeaderRoots (bin / "clang") do
      emitDirectory directory
    let abiLibraries := bin / "../sysroot/usr/lib/aarch64-linux-android"
    for file in ← abiLibraries.readDir do
      unless (← file.path.isDir) do emit file.path
    emitDirectory (abiLibraries / "26")
    let resource ← Runner.execute (bin / "clang").toString #["-print-resource-dir"]
    let builtins := FilePath.mk resource.trimAscii.toString / "lib/linux"
    for file in ← builtins.readDir do
      if file.fileName.endsWith "-aarch64-android.a" then emit file.path
    return
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
    let modules ← runtimeModules workspace app
    IO.Process.setCurrentDir package
    try
      let _ ← Runner.execute (toolchain / "bin/lake").toString #["build"]
      let _ ← Runner.execute (toolchain / "bin/lake").toString <|
        #["build"] ++ modules.map (fun module => s!"+{module.name}:c")
    finally
      IO.Process.setCurrentDir previous
    let sources := modules.map (fun module => module.cFile.toString)
    let sourceList := work / "package-sources.json"
    IO.FS.writeFile sourceList (Lean.toJson sources |>.compress)
    let initializer := Lean.mkModuleInitializationFunctionName app.name app.pkg.id? .runtime
    let libraryPath := project / ".lake/build/lib/lean"
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
