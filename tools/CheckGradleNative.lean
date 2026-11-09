import Std

namespace CheckGradleNative

structure Config where
  project : System.FilePath
  gradle : System.FilePath
  jdk : System.FilePath
  cache : System.FilePath
  output : System.FilePath

def contains (text needle : String) : Bool := (text.splitOn needle).length > 1

def rejectedNative (code : UInt32) (log : String) : Bool :=
  code != 0 && contains log "UnsatisfiedLinkError"

theorem success_is_not_rejection (log : String) : rejectedNative 0 log = false := by
  simp [rejectedNative]

theorem unrelated_failure_is_not_rejection (code : UInt32) (log : String)
    (h : contains log "UnsatisfiedLinkError" = false) : rejectedNative code log = false := by
  simp [rejectedNative, h]

def verdict (baseline unchanged changed restored : IO.Process.Output) : Except String Unit := do
  unless baseline.exitCode == 0 do throw "Passing native baseline failed"
  unless unchanged.exitCode == 0 && contains unchanged.stdout ":wire:test UP-TO-DATE" do
    throw "Unchanged native input did not reuse its successful test result"
  unless rejectedNative changed.exitCode (changed.stdout ++ changed.stderr) do
    throw "Changed native input did not trigger the expected JNI loading failure"
  unless restored.exitCode == 0 do throw "Restored native input failed"

theorem cached_success_refused (baseline unchanged changed restored : IO.Process.Output)
    (hb : baseline.exitCode = 0) (hu : unchanged.exitCode = 0)
    (hs : contains unchanged.stdout ":wire:test UP-TO-DATE" = true)
    (hc : changed.exitCode = 0) :
    verdict baseline unchanged changed restored =
      .error "Changed native input did not trigger the expected JNI loading failure" := by
  simp [verdict, hb, hu, hs, rejectedNative, hc, bind, Except.bind, pure, throw]
  rfl

theorem valid_sequence_accepted (baseline unchanged changed restored : IO.Process.Output)
    (hb : baseline.exitCode = 0) (hu : unchanged.exitCode = 0)
    (hs : contains unchanged.stdout ":wire:test UP-TO-DATE" = true)
    (hc : rejectedNative changed.exitCode (changed.stdout ++ changed.stderr) = true)
    (hr : restored.exitCode = 0) : verdict baseline unchanged changed restored = .ok () := by
  simp [verdict, hb, hu, hs, hc, hr, pure]
  rfl

def arguments (library : System.FilePath) : Array String := #[
  "--offline", "--no-daemon", "--console=plain", "--max-workers=4", "-Dorg.gradle.jvmargs=",
  "-PwireLibrary=" ++ library.toString, ":wire:test"]

theorem selected_library (library : System.FilePath) :
    (arguments library)[5]? = some ("-PwireLibrary=" ++ library.toString) := rfl

def run (config : Config) (library : System.FilePath) (stage : String) : IO IO.Process.Output := do
  let result ← IO.Process.output {
    cmd := config.gradle.toString, args := arguments library, cwd := some config.project,
    env := #[("JAVA_HOME", some config.jdk.toString), ("GRADLE_USER_HOME", some config.cache.toString)] }
  IO.FS.writeFile (config.output / s!"{stage}.log") (result.stdout ++ result.stderr)
  IO.println s!"{stage}: exit {result.exitCode}; test up-to-date={contains result.stdout ":wire:test UP-TO-DATE"}; JNI load failure={contains (result.stdout ++ result.stderr) "UnsatisfiedLinkError"}"
  return result

def runGood (config : Config) (library : System.FilePath) (stage : String) : IO IO.Process.Output := do
  let result ← run config library stage
  if result.exitCode != 0 then throw (IO.userError s!"{stage} failed; native mutation was not attempted")
  return result

def check (config : Config) : IO Unit := do
  let source := config.project / "host/wire/build/native/libkotlean_wire_test.so"
  for path in [config.project / "settings.gradle.kts", config.gradle, config.jdk / "bin/java", source] do
    unless ← path.pathExists do throw (IO.userError s!"Missing prerequisite: {path}")
  if ← config.output.pathExists then
    unless (← config.output.readDir).isEmpty do
      throw (IO.userError "Evidence directory must be empty")
  else IO.FS.createDirAll config.output
  let library := config.output / "native-input.so"
  let original ← IO.FS.readBinFile source
  let mut results : Option (IO.Process.Output × IO.Process.Output × IO.Process.Output) := none
  try
    IO.FS.writeBinFile library original
    try
      let baseline ← runGood config library "baseline"
      let unchanged ← runGood config library "unchanged"
      IO.FS.writeBinFile library ByteArray.empty
      let changed ← run config library "changed"
      results := some (baseline, unchanged, changed)
    finally
      IO.FS.writeBinFile library original
    let restored ← run config library "restored"
    let some (baseline, unchanged, changed) := results
      | throw (IO.userError "Native-input control did not finish")
    match verdict baseline unchanged changed restored with
    | .ok () => IO.println "Gradle native-input tracking passed: unchanged skips, changed runs, restored passes"
    | .error message => throw (IO.userError message)
  finally
    if ← library.pathExists then IO.FS.removeFile library

end CheckGradleNative

def main (args : List String) : IO Unit := do
  let [project, gradle, jdk, cache, output] := args
    | throw (IO.userError "Usage: lean --run tools/CheckGradleNative.lean PROJECT GRADLE JDK CACHE EVIDENCE_DIRECTORY")
  CheckGradleNative.check ⟨project, gradle, jdk, cache, output⟩
