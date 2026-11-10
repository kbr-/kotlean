import KotleanBuild.Runner

open System KotleanBuild

def main (args : List String) : IO Unit := do
  let [cli, package, directory] := args
    | throw (IO.userError "Usage: lean --run tools/BuildConcurrency.lean CLI PACKAGE EMPTY_DIRECTORY")
  let work : FilePath := directory
  if ← work.pathExists then throw (IO.userError "Evidence directory must be new")
  IO.FS.createDirAll work
  let run := fun module (output : FilePath) => do
    let result ← IO.Process.output {cmd := cli, args := #["build", package, module, output.toString]}
    IO.FS.writeFile (output.withExtension "log") (result.stdout ++ result.stderr)
    unless result.exitCode == 0 do throw (IO.userError s!"Build {module} failed: {result.stderr}")
    Runner.digest output
  let nat ← run "ExportNat" (work / "nat-reference.so")
  let text ← run "ExportText" (work / "text-reference.so")
  let natTask ← IO.asTask (run "ExportNat" (work / "nat-concurrent.so")) .dedicated
  let textTask ← IO.asTask (run "ExportText" (work / "text-concurrent.so")) .dedicated
  let natResult := natTask.get
  let textResult := textTask.get
  let actualNat ← IO.ofExcept natResult
  let actualText ← IO.ofExcept textResult
  unless actualNat == nat && actualText == text && nat != text do
    throw (IO.userError "Concurrent builds differ from distinct sequential app libraries")
  IO.println "Concurrent app builds: both complete libraries equal their distinct sequential references"
