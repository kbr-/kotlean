module
public import Std
public import KotleanBuild.Policy

@[expose] public section

namespace KotleanBuild.Runner
open System KotleanBuild

def execute (command : String) (arguments : Array String) : IO String := do
  let result ← IO.Process.output {cmd := command, args := arguments}
  if result.exitCode != 0 then
    IO.eprint result.stderr
    throw (IO.userError s!"Command failed ({result.exitCode}): {command}")
  return result.stdout

def digest (path : FilePath) : IO String := do
  let output ← execute "cmake" #["-E", "sha256sum", path.toString]
  return (output.take 64).toString

def filesUnder (directory : FilePath) : IO (Array FilePath) := do
  let files ← (← directory.walkDir).filterM fun path => do
    return !(← path.isDir)
  return files.qsort (fun left right => left.toString < right.toString)

def directoryDigest (directory : FilePath) (includeFile : FilePath → Bool := fun _ => true) :
    IO String := do
  let files := (← filesUnder directory).filter includeFile
  IO.FS.withTempFile fun handle manifest => do
    for start in [:files.size:256] do
      let paths := files.extract start (start + 256)
      handle.putStr (← execute "cmake" (#["-E", "sha256sum"] ++ paths.map FilePath.toString))
    handle.flush
    digest manifest

def androidHeaderRoots (compiler : FilePath) : IO (List FilePath) := do
  let resource ← execute compiler.toString #["-print-resource-dir"]
  let ndkToolchain := compiler.parent.bind FilePath.parent
  let some ndkToolchain := ndkToolchain | throw (IO.userError "Missing NDK toolchain directory")
  return [ndkToolchain / "sysroot/usr/include", FilePath.mk resource.trimAscii.toString / "include"]

def androidLeanHeaders (compiler work : FilePath) : IO String := do
  let roots ← androidHeaderRoots compiler
  let headers ← (roots ++ [work / "include/lean"]).mapM (fun root => directoryDigest root)
  return (← digest compiler) ++ String.join headers

def observe (work : FilePath) (relative : String) : IO Observations := do
  let path := work / relative
  if ← path.pathExists then return [(relative, some (← digest path))]
  return [(relative, none)]

def readManifest (path : FilePath) : IO (Option Manifest) := do
  if !(← path.pathExists) then return none
  let text ← IO.FS.readFile path
  return (Lean.Json.parse text >>= Lean.fromJson?).toOption

def runStage (work receipt : FilePath) (signature : Signature) (relative step command : String)
    (arguments : Array String) : IO Bool := do
  let previous ← readManifest receipt
  if cacheHit signature [relative] previous (← observe work relative) then return false
  let _ ← execute command arguments
  let some manifest := finishCache signature [relative] [step] [(step, 0)] (← observe work relative)
    | throw (IO.userError s!"Successful command left no complete artifact: {relative}")
  IO.FS.createDirAll (receipt.parent.getD ".")
  let temporary := receipt.toString ++ ".tmp"
  IO.FS.writeFile temporary (Lean.toJson manifest |>.compress)
  IO.FS.rename temporary receipt
  return true

def buildUnit (toolchain ndk work sourceRoot source : FilePath) (context headers : String) : IO Unit := do
  let some suffix := source.toString.dropPrefix? (sourceRoot.toString ++ "/")
    | throw (IO.userError s!"Source outside pinned standard library: {source}")
  let relative : FilePath := suffix.toString
  let generated := FilePath.mk "gen" / relative.withExtension "c"
  let object := FilePath.mk "obj" / relative.withExtension "o"
  IO.FS.createDirAll ((work / generated).parent.getD ".")
  IO.FS.createDirAll ((work / object).parent.getD ".")
  let sourceDigest ← digest source
  let generation : Signature := ⟨1, context, .linuxX86_64, "", "", ["-j1"],
    [⟨relative.toString, sourceDigest⟩]⟩
  let genReceipt := work / "receipts/gen" / relative.withExtension "json"
  let generatedNow ← runStage work genReceipt generation generated.toString "generate"
    (toolchain / "bin/lean").toString
    #["-j1", "--root=" ++ sourceRoot.toString, "-c", (work / generated).toString, source.toString]
  let cDigest ← digest (work / generated)
  let compilation : Signature := ⟨1, context, .androidArm64, "r30-api26", "",
    ["-O2", "-fPIC", "-ffunction-sections", "-fdata-sections"],
    [⟨generated.toString, cDigest⟩, ⟨"headers", headers⟩]⟩
  let objReceipt := work / "receipts/obj" / relative.withExtension "json"
  let compiledNow ← runStage work objReceipt compilation object.toString "compile"
    (ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin/clang").toString
    #["--target=aarch64-linux-android26", "-O2", "-fPIC", "-ffunction-sections", "-fdata-sections",
      "-I" ++ (work / "include").toString, "-c", (work / generated).toString,
      "-o", (work / object).toString]
  IO.println s!"{relative}: generated={generatedNow} compiled={compiledNow}"
  (← IO.getStdout).flush

def runWorker (queue : Std.Mutex (List FilePath)) (action : FilePath → IO Unit) : IO Unit := do
  repeat
    let next ← queue.atomically do
      let pending ← get
      set pending.tail
      return pending.head?
    let some source := next | return
    try
      action source
    catch error =>
      queue.atomically (set ([] : List FilePath))
      throw error

def parallel (files : Array FilePath) (jobs : Nat) (action : FilePath → IO Unit) : IO Unit := do
  let queue ← Std.Mutex.new files.toList
  let tasks ← (List.range jobs).mapM fun _ => IO.asTask (runWorker queue action)
  let mut failure : Option IO.Error := none
  for task in tasks do
    match task.get with
    | .ok _ => pure ()
    | .error error => failure := some error
  if let some error := failure then throw error

end KotleanBuild.Runner
