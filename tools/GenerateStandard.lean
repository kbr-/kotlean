import KotleanBuild.Runner

def main (args : List String) : IO Unit := do
  let [toolchain, ndk, work, jobsText, selection] := args
    | throw (IO.userError "Usage: lean --run tools/GenerateStandard.lean TOOLCHAIN NDK WORK JOBS all|MODULE")
  let some jobs := jobsText.toNat? | throw (IO.userError "JOBS must be a positive integer")
  if jobs == 0 then throw (IO.userError "JOBS must be positive")
  let base ← IO.currentDir
  let toolchain := base / toolchain
  let ndk := base / ndk
  let work := base / work
  let sourceRoot := toolchain / "src/lean"
  let mut files := #[sourceRoot / "Init.lean", sourceRoot / "Std.lean"]
  for directory in [sourceRoot / "Init", sourceRoot / "Std"] do
    files := files ++ (← directory.walkDir).filter (fun path => path.extension == some "lean")
  files := files.qsort (fun left right => left.toString < right.toString)
  if selection != "all" then
    let selected := Lean.modToFilePath sourceRoot selection.toName "lean"
    files := files.filter (· == selected)
  if files.isEmpty then throw (IO.userError "No standard-library source selected")
  let version ← KotleanBuild.Runner.execute (toolchain / "bin/lean").toString #["--version"]
  let context := version ++ (← KotleanBuild.Runner.digest (toolchain / "lib/lean/libleanshared.so"))
  let bin := ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin"
  let compiler := bin / "clang"
  let archiver := bin / "llvm-ar"
  let headers ← KotleanBuild.Runner.androidLeanHeaders compiler work
  IO.println s!"Standard units: {files.size}; workers: {jobs}; selected: {selection}"
  (← IO.getStdout).flush
  let lock ← IO.FS.Handle.mk (work / ".standard.lock") .append
  lock.lock
  try
    let sourceHashes ← KotleanBuild.Runner.execute "cmake" <|
      #["-E", "sha256sum"] ++ files.map System.FilePath.toString
    let archiveSignature : KotleanBuild.Signature := ⟨1, context, .androidArm64, headers,
      ← KotleanBuild.Runner.digest archiver,
      ["-O2", "-fPIC", "-ffunction-sections", "-fdata-sections"], [⟨"sources", sourceHashes⟩]⟩
    let archiveReceipt := work / "receipts/standard-archive.json"
    if selection == "all" && KotleanBuild.cacheHit archiveSignature ["libstandard.a"]
        (← KotleanBuild.Runner.readManifest archiveReceipt)
        (← KotleanBuild.Runner.observe work "libstandard.a") then
      IO.println "Standard archive reused: complete matching inputs and bytes"
      return
    KotleanBuild.Runner.parallel files jobs fun source =>
      KotleanBuild.Runner.buildUnit toolchain ndk work sourceRoot source context headers
    if selection == "all" then
      let mut objects := #[]
      for source in files do
        let some suffix := source.toString.dropPrefix? (sourceRoot.toString ++ "/")
          | throw (IO.userError "Standard source outside configured root")
        objects := objects.push (work / "obj" / System.FilePath.mk suffix.toString |>.withExtension "o")
      if ← (work / "libstandard.a").pathExists then IO.FS.removeFile (work / "libstandard.a")
      let _ ← KotleanBuild.Runner.runStage work archiveReceipt archiveSignature "libstandard.a" "archive"
        archiver.toString
        (#["rcs", (work / "libstandard.a").toString] ++ objects.map System.FilePath.toString)
    IO.println s!"Standard compilation complete: {files.size} units"
  finally
    lock.unlock
