import Std

namespace BuildWireNative

structure Config where
  project : System.FilePath
  toolchain : System.FilePath
  jdk : System.FilePath

structure Command where
  executable : String
  arguments : Array String
  directory : System.FilePath

def requirements (c : Config) : List System.FilePath := [
  c.toolchain / "bin/lake", c.toolchain / "bin/leanc", c.toolchain / "include/lean/lean.h",
  c.toolchain / "lib/lean/libleanshared.so", c.jdk / "include/jni.h", c.jdk / "include/linux/jni_md.h",
  c.jdk / "bin/java", c.jdk / "bin/javac",
  c.project / "lean/lakefile.toml", c.project / "native/include/kotlean_jni.hpp",
  c.project / "host/wire/src/test/cpp/wire_jni.cpp",
  c.project / "host/wire/src/control/java/io/kotlean/WireNative.java"
]

def directory (c : Config) : System.FilePath := c.project / "host/wire/build/native"
def destination (c : Config) : System.FilePath := directory c / "libkotlean_wire_test.so"
def temporary (c : Config) : System.FilePath := directory c / "libkotlean_wire_test.so.tmp"

def commands (c : Config) : Array Command := #[
  ⟨(c.toolchain / "bin/lake").toString, #["build", "KotleanTest:static", "Kotlean:static"],
    c.project / "lean"⟩,
  ⟨"c++", #["-c", "-fPIC", "-std=c++17", "-fno-exceptions", "-fno-rtti",
    "-I" ++ (c.toolchain / "include").toString,
    "-I" ++ (c.jdk / "include").toString, "-I" ++ (c.jdk / "include/linux").toString,
    "-I" ++ (c.project / "native/include").toString,
    (c.project / "host/wire/src/test/cpp/wire_jni.cpp").toString,
    "-o", (directory c / "wire_jni.o").toString], c.project⟩,
  ⟨(c.toolchain / "bin/leanc").toString, #["-shared", "-fPIC",
    (directory c / "wire_jni.o").toString,
    "-Wl,-z,defs", "-Wl,--start-group",
    (c.project / "lean/.lake/build/lib/libkotlean_KotleanTest.a").toString,
    (c.project / "lean/.lake/build/lib/libkotlean_Kotlean.a").toString,
    "-Wl,--end-group",
    "-L" ++ (c.toolchain / "lib/lean").toString, "-lleanshared",
    "-Wl,-rpath," ++ (c.toolchain / "lib/lean").toString,
    "-o", (temporary c).toString], c.project⟩,
  ⟨(c.jdk / "bin/javac").toString,
    #["-d", (directory c / "classes").toString,
      (c.project / "host/wire/src/control/java/io/kotlean/WireNative.java").toString], c.project⟩,
  ⟨(c.jdk / "bin/java").toString,
    #["-cp", (directory c / "classes").toString, "io.kotlean.WireNative",
      (temporary c).toString], c.project⟩
]

def prepare (missing : List System.FilePath) (c : Config) : Except String (Array Command) :=
  match missing with
  | [] => .ok (commands c)
  | first :: _ => .error s!"Missing build prerequisite: {first}"

theorem missing_refuses (first : System.FilePath) (rest : List System.FilePath) (c : Config) :
    prepare (first :: rest) c = .error s!"Missing build prerequisite: {first}" := rfl

theorem ready_plan (c : Config) : prepare [] c = .ok (commands c) := rfl

theorem prerequisite_count (c : Config) : (requirements c).length = 12 := rfl

theorem output_in_build (c : Config) :
    destination c = c.project / "host/wire/build/native" / "libkotlean_wire_test.so" := rfl

def memoryCommands (c : Config) : Array Command :=
  #["stress", "leak"].map fun mode =>
    ⟨(c.jdk / "bin/java").toString,
      #["-Xms64m", "-Xmx64m", "-cp", (directory c / "classes").toString,
        "io.kotlean.WireNative", (destination c).toString, mode], c.project⟩

theorem memory_control_pair (c : Config) : (memoryCommands c).size = 2 := by
  simp [memoryCommands]

def execute (command : Command) : IO Unit := do
  IO.println s!"Running {command.executable} {String.intercalate " " command.arguments.toList}"
  let result ← IO.Process.output {
    cmd := command.executable, args := command.arguments, cwd := some command.directory }
  IO.print result.stdout
  IO.eprint result.stderr
  if result.exitCode != 0 then
    throw (IO.userError s!"Build command failed with exit {result.exitCode}")

end BuildWireNative

def main (args : List String) : IO Unit := do
  let (args, memoryTest) := if args.getLast? == some "--memory-test" then (args.dropLast, true) else (args, false)
  let [project, toolchain, jdk] := args
    | throw (IO.userError "Usage: lean --run tools/BuildWireNative.lean PROJECT TOOLCHAIN JDK [--memory-test]")
  let base ← IO.currentDir
  let config : BuildWireNative.Config := ⟨base / project, base / toolchain, base / jdk⟩
  let mut missing := []
  for path in BuildWireNative.requirements config do
    unless ← path.pathExists do missing := missing ++ [path]
  let .ok commands := BuildWireNative.prepare missing config
    | throw (IO.userError (String.intercalate "\n" (missing.map fun path => s!"Missing: {path}")))
  IO.FS.createDirAll (BuildWireNative.directory config)
  IO.FS.createDirAll (BuildWireNative.directory config / "classes")
  for command in commands do BuildWireNative.execute command
  IO.FS.rename (BuildWireNative.temporary config) (BuildWireNative.destination config)
  IO.println s!"Native wire library: {BuildWireNative.destination config}"
  if memoryTest then
    let tasks ← (BuildWireNative.memoryCommands config).mapM fun command =>
      IO.asTask (BuildWireNative.execute command)
    for task in tasks do IO.ofExcept task.get
