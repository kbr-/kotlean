import KotleanBuild.Runner

open System KotleanBuild

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [workText, compilerText, ndkText, cli, package] := args
    | throw (IO.userError "Usage: lean --run tools/BuildIntegration.lean EMPTY_DIRECTORY CLANG NDK CLI PACKAGE")
  let work : FilePath := workText
  ensure (!(← work.pathExists)) "Integration directory must be new"
  IO.FS.createDirAll work
  let refusedCache := work / "refused-cache"
  let refusedOutput := work / "refused.so"
  let refused ← IO.Process.output {
    cmd := cli, args := #["build", package, "ExportText", refusedOutput.toString]
    env := #[("KOTLEAN_CACHE", some refusedCache.toString),
      ("KOTLEAN_LIBUV_SOURCE", some (work / "missing-libuv").toString)]
  }
  ensure (refused.exitCode != 0 && refused.stderr.contains "Missing prerequisite")
    "Missing dependency did not produce preflight refusal"
  ensure (!(← refusedCache.pathExists) && !(← refusedOutput.pathExists))
    "Preflight refusal changed configured cache/output"
  let source := work / "input.c"
  let object := work / "output.o"
  let receipt := work / "receipt.json"
  IO.FS.writeFile source "int value(void) { return 17; }\n"
  let sourceHash ← Runner.digest source
  let independent ← Runner.execute "sha256sum" #[source.toString]
  ensure (sourceHash == (independent.take 64).toString) "File digest disagrees with sha256sum"
  let signature : Signature := ⟨1, "fixture", .linuxX86_64, "ndk", "uv", ["-O2"],
    [⟨"input.c", sourceHash⟩]⟩
  let build := fun sig => Runner.runStage work receipt sig "output.o" "compile" compilerText
    #["-O2", "-c", source.toString, "-o", object.toString]
  ensure (← build signature) "First compiler execution was skipped"
  let original ← IO.FS.readBinFile object
  ensure (!(← build signature)) "Unchanged artifact was rebuilt"
  IO.FS.writeFile object "incomplete compiler output"
  ensure (← build signature) "Corrupted artifact was accepted"
  ensure ((← IO.FS.readBinFile object) == original) "Corrupted object was not restored"
  IO.FS.removeFile object
  ensure (← build signature) "Missing artifact was accepted"
  IO.FS.writeFile receipt "{incomplete"
  ensure (← build signature) "Interrupted manifest was accepted"
  for changed in [
      { signature with format := 2 },
      { signature with toolchain := "other" },
      { signature with abi := .androidArm64 },
      { signature with ndk := "other" },
      { signature with libuv := "other" },
      { signature with flags := ["-O0"] },
      { signature with inputs := [⟨"input.c", "other"⟩] }] do
    ensure (← build changed) "Changed signature was accepted as cached"
    ensure (!(← build changed)) "Changed signature did not become reusable"
    ensure (← build signature) "Original signature was confused with changed signature"
  IO.FS.writeFile source "int value(void) { return 29; }\n"
  let changedHash ← Runner.digest source
  ensure (sourceHash != changedHash) "Changed bytes retained their digest"
  let changed := { signature with inputs := [⟨"input.c", changedHash⟩] }
  ensure (← build changed) "Changed source was skipped"
  ensure ((← IO.FS.readBinFile object) != original) "Changed source left the old object"
  let accepted ← IO.FS.readFile receipt
  IO.FS.writeFile source "this is not valid C\n"
  let mut failed := false
  try
    let _ ← build { changed with toolchain := "failed-compiler" }
  catch _ => failed := true
  ensure failed "Real compiler error was swallowed"
  ensure ((← IO.FS.readFile receipt) == accepted) "Failed compilation published completion"
  IO.FS.writeFile source "int value(void) { return 29; }\n"
  let _ ← build changed
  ensure (!(← build changed)) "Successful retry did not repair compiler output"
  let lockFile := work / "cache.lock"
  let lock ← IO.FS.Handle.mk lockFile .append
  lock.lock
  let excluded ← IO.Process.output {cmd := "flock", args := #["--nonblock", lockFile.toString, "true"]}
  ensure (excluded.exitCode == 1) "Independent OS client entered a held lock"
  lock.unlock
  let _ ← Runner.execute "flock" #["--nonblock", lockFile.toString, "true"]
  let holder ← IO.Process.spawn {
    cmd := "flock", args := #["--no-fork", lockFile.toString, "cat"]
    stdin := .piped, stdout := .piped
  }
  try
    holder.stdin.putStrLn "lock acquired"
    holder.stdin.flush
    ensure ((← holder.stdout.getLine) == "lock acquired\n") "Lock holder did not acknowledge entry"
    let excluded ← IO.Process.output {cmd := "flock", args := #["--nonblock", lockFile.toString, "true"]}
    ensure (excluded.exitCode == 1) "Concurrent process entered held lock"
  finally
    holder.kill
    let _ ← holder.wait
  let _ ← Runner.execute "flock" #["--nonblock", lockFile.toString, "true"]
  let localSource := work / "local-libc.c"
  let localObject := work / "local-libc.o"
  IO.FS.writeFile localSource "__attribute__((used,noinline)) static void free(void *p) { (void)p; }\n"
  let _ ← Runner.execute compilerText #["--target=aarch64-linux-android26", "-fPIC", "-c",
    localSource.toString, "-o", localObject.toString]
  let bin := FilePath.mk ndkText / "toolchains/llvm/prebuilt/linux-x86_64/bin"
  let defined ← Runner.execute (bin / "llvm-nm").toString #["-j", "--defined-only", localObject.toString]
  let libc ← Runner.execute (bin / "llvm-nm").toString #["-D", "-j", "--defined-only",
    (FilePath.mk ndkText / "toolchains/llvm/prebuilt/linux-x86_64/sysroot/usr/lib/aarch64-linux-android/26/libc.so").toString]
  let libcNames := libc.splitOn "\n" |>.filter (· != "") |>.map (fun name => (name.splitOn "@").head!)
  ensure ((clashes (defined.splitOn "\n" |>.filter (· != "")) libcNames).contains "free") "Local libc replacement escaped detection"
  let ordinary ← Runner.execute (bin / "llvm-nm").toString #["-j", "--defined-only", object.toString]
  ensure ((clashes (ordinary.splitOn "\n" |>.filter (· != "")) libcNames).isEmpty) "Ordinary object was rejected"
  IO.println "Build I/O: preflight isolation, real hashes, unchanged reuse, corruption, missing/interrupted artifacts, all signature fields, compiler failure, OS lock exclusion/process-death release and local libc control passed"
