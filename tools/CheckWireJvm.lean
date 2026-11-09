import Std

namespace CheckWireJvm

structure Artifact where
  group : String
  name : String
  version : String

def artifacts : List Artifact := [
  ⟨"org.jetbrains.kotlin", "kotlin-compiler-embeddable", "2.2.10"⟩,
  ⟨"org.jetbrains.kotlin", "kotlin-stdlib", "2.2.10"⟩,
  ⟨"org.jetbrains.kotlin", "kotlin-script-runtime", "2.2.10"⟩,
  ⟨"org.jetbrains.kotlin", "kotlin-reflect", "1.6.10"⟩,
  ⟨"org.jetbrains.kotlin", "kotlin-daemon-embeddable", "2.2.10"⟩,
  ⟨"org.jetbrains.kotlinx", "kotlinx-coroutines-core-jvm", "1.8.0"⟩,
  ⟨"org.jetbrains", "annotations", "13.0"⟩
]

def jarName (artifact : Artifact) : String := s!"{artifact.name}-{artifact.version}.jar"

def select (paths : List System.FilePath) : Except String System.FilePath :=
  match paths with
  | [path] => .ok path
  | [] => .error "Missing cached artifact; no download was attempted"
  | _ => .error "Ambiguous cached artifact"

theorem singleton_selected (path : System.FilePath) : select [path] = .ok path := rfl
theorem missing_refused : select [] = .error "Missing cached artifact; no download was attempted" := rfl
theorem expected_count : artifacts.length = 7 := rfl
theorem compiler_name : (artifacts.map jarName).head? =
    some "kotlin-compiler-embeddable-2.2.10.jar" := rfl

def cached (cache : System.FilePath) (artifact : Artifact) : IO System.FilePath := do
  let directory := cache / "caches/modules-2/files-2.1" / artifact.group / artifact.name / artifact.version
  let mut candidates := []
  for entry in ← directory.readDir do
    let path := entry.path / jarName artifact
    if ← path.pathExists then candidates := candidates ++ [path]
  match select candidates with
  | .ok path => return path
  | .error message => throw (IO.userError s!"{artifact.group}:{artifact.name}:{artifact.version}: {message}")

def execute (jdk : System.FilePath) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := (jdk / "bin/java").toString, args := args }
  IO.print result.stdout
  IO.eprint result.stderr
  if result.exitCode != 0 then throw (IO.userError s!"JVM command failed with exit {result.exitCode}")

structure Mutation where
  name : String
  file : String := "Wire.kt"
  before : String
  after : String
  marker : String

def mutations : List Mutation := [
  { name := "empty-event", before := "}.finish()\n    fun encodeInit",
    after := "}.finish().let { ByteArray(0) }\n    fun encodeInit", marker := "event seed=" },
  { name := "swapped-node-fields", before := "natural(value.revision); natural(value.id); input(value.input)",
    after := "natural(value.id); natural(value.revision); input(value.input)", marker := "event seed=" },
  { name := "truncated-natural", before := "var rest = value",
    after := "var rest = value.and(BigInteger.valueOf(Long.MAX_VALUE))", marker := "event seed=" },
  { name := "ignored-trailing", before := "fun end() { if (position != limit) throw WireException(\"Trailing protocol bytes\") }",
    after := "fun end() {}", marker := "grammar index=" },
  { name := "noncanonical-natural", before := "if (shift != 0 && digit == 0) throw WireException(\"Noncanonical natural field\")",
    after := "Unit", marker := "grammar index=" },
  { name := "lossy-utf8", before := "newDecoder().onMalformedInput(CodingErrorAction.REPORT)",
    after := "newDecoder().onMalformedInput(CodingErrorAction.REPLACE)", marker := "grammar index=" },
  { name := "color-overflow", before := "if (value.bitLength() > 32) throw WireException(\"Color exceeds unsigned 32-bit range\")",
    after := "Unit", marker := "grammar index=" },
  { name := "zeroing-transport", file := "WireNative.kt",
    before := "fun echo(bytes: ByteArray): ByteArray = call { WireNative.echo(bytes) }",
    after := "fun echo(bytes: ByteArray): ByteArray = call { WireNative.echo(bytes) }.also { it.fill(0) }",
    marker := "transport seed=" }
]

def replaceUnique (pieces : List String) (replacement : String) : Except String String :=
  match pieces with
  | [before, after] => .ok (before ++ replacement ++ after)
  | _ => .error "Mutation source must contain exactly one match"

theorem unique_replacement (before after replacement : String) :
    replaceUnique [before, after] replacement = .ok (before ++ replacement ++ after) := rfl

theorem absent_replacement (whole replacement : String) :
    replaceUnique [whole] replacement = .error "Mutation source must contain exactly one match" := rfl

theorem mutation_count : mutations.length = 8 := rfl

def sourceFiles (project : System.FilePath) (overrideFile : Option (String × System.FilePath)) :
    Array System.FilePath :=
  let source := project / "host/wire/src"
  let wire := match overrideFile with
    | some ("Wire.kt", path) => path | _ => source / "main/kotlin/io/kotlean/Wire.kt"
  let native := match overrideFile with
    | some ("WireNative.kt", path) => path | _ => source / "test/kotlin/io/kotlean/WireNative.kt"
  #[source / "main/kotlin/io/kotlean/Protocol.kt", wire,
    source / "test/kotlin/io/kotlean/Fixture.kt", native,
    source / "control/kotlin/io/kotlean/WireControl.kt"]

theorem five_sources (project : System.FilePath) (overrideFile) :
    (sourceFiles project overrideFile).size = 5 := rfl

def compileArgs (classpath : String) (stdlib output : System.FilePath)
    (files : Array System.FilePath) : Array String :=
  #["-XX:ActiveProcessorCount=4", "-cp", classpath, "org.jetbrains.kotlin.cli.jvm.K2JVMCompiler",
    "-no-stdlib", "-no-reflect", "-Werror", "-jvm-target", "17", "-classpath", stdlib.toString,
    "-d", output.toString] ++ files.map System.FilePath.toString

def controlArgs (project output stdlib : System.FilePath) : Array String := #[
  "-XX:ActiveProcessorCount=4",
  "-Dkotlean.wire.library=" ++ (project / "host/wire/build/native/libkotlean_wire_test.so").toString,
  "-cp", output.toString ++ ":" ++ stdlib.toString, "io.kotlean.WireControlKt"]

theorem compiler_entry (classpath : String) (stdlib output : System.FilePath) (files) :
    (compileArgs classpath stdlib output files)[3]? =
      some "org.jetbrains.kotlin.cli.jvm.K2JVMCompiler" := by
  simp [compileArgs, Array.getElem?_append]

theorem control_main (project output stdlib : System.FilePath) :
    (controlArgs project output stdlib).back? = some "io.kotlean.WireControlKt" := rfl

def mutate (project jdk stdlib : System.FilePath) (classpath : String) (mutation : Mutation) : IO Bool := do
  let directory := project / "host/wire/build/mutants" / mutation.name
  IO.FS.createDirAll directory
  let original := if mutation.file == "Wire.kt" then
    project / "host/wire/src/main/kotlin/io/kotlean/Wire.kt" else
    project / "host/wire/src/test/kotlin/io/kotlean/WireNative.kt"
  let text ← IO.FS.readFile original
  let .ok patched := replaceUnique (text.splitOn mutation.before) mutation.after
    | throw (IO.userError s!"Invalid exact mutation: {mutation.name}")
  let path := directory / mutation.file
  IO.FS.writeFile path patched
  let output := directory / "classes"
  IO.FS.createDirAll output
  let compiled ← IO.Process.output {
    cmd := (jdk / "bin/java").toString
    args := compileArgs classpath stdlib output (sourceFiles project (some (mutation.file, path))) }
  IO.FS.writeFile (directory / "compile.log") (compiled.stdout ++ compiled.stderr)
  if compiled.exitCode != 0 then
    IO.println s!"BROKEN {mutation.name}: compilation failed"
    return false
  let result ← IO.Process.output {
    cmd := (jdk / "bin/java").toString
    args := controlArgs project output stdlib }
  let log := result.stdout ++ result.stderr
  IO.FS.writeFile (directory / "control.log") log
  let killed := result.exitCode == 1 && (log.splitOn mutation.marker).length > 1
  IO.println s!"{if killed then "KILLED" else if result.exitCode == 0 then "SURVIVED" else "BROKEN"} {mutation.name} by {mutation.marker}"
  return killed

end CheckWireJvm

def main (args : List String) : IO Unit := do
  let (args, runMutations) := if args.getLast? == some "--mutations" then (args.dropLast, true) else (args, false)
  let [project, cache, jdk] := args
    | throw (IO.userError "Usage: lean --run tools/CheckWireJvm.lean PROJECT GRADLE_CACHE JDK [--mutations]")
  let project : System.FilePath := project
  let cache : System.FilePath := cache
  let jdk : System.FilePath := jdk
  let jars ← CheckWireJvm.artifacts.mapM (CheckWireJvm.cached cache)
  let classpath := String.intercalate ":" (jars.map System.FilePath.toString)
  let stdlib := jars[1]!
  let output := project / "host/wire/build/control-kotlin"
  IO.FS.createDirAll output
  CheckWireJvm.execute jdk (CheckWireJvm.compileArgs classpath stdlib output
    (CheckWireJvm.sourceFiles project none))
  CheckWireJvm.execute jdk (CheckWireJvm.controlArgs project output stdlib)
  if runMutations then
    let worker := fun (items : List CheckWireJvm.Mutation) => do
      let mut passed := true
      for mutation in items do
        let killed ← CheckWireJvm.mutate project jdk stdlib classpath mutation
        passed := passed && killed
      return passed
    let first ← IO.asTask (worker (CheckWireJvm.mutations.take 4))
    let second ← IO.asTask (worker (CheckWireJvm.mutations.drop 4))
    let firstResult ← IO.ofExcept first.get
    let secondResult ← IO.ofExcept second.get
    unless firstResult && secondResult do throw (IO.userError "Mutation batch has a survivor or broken case")
    IO.println s!"Mutation batch passed: {CheckWireJvm.mutations.length} killed after passing control"
