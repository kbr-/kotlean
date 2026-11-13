import Std

namespace BuildAppNative

structure Config where
  project : System.FilePath
  toolchain : System.FilePath
  jdk : System.FilePath
  source : System.FilePath
  initializer : String
  output : System.FilePath

structure Command where
  executable : String
  arguments : Array String
  directory : System.FilePath

def requirements (c : Config) : List System.FilePath := [
  c.toolchain / "bin/lake", c.toolchain / "bin/leanc", c.toolchain / "include/lean/lean.h",
  c.toolchain / "lib/lean/libleanshared.so", c.jdk / "include/jni.h", c.jdk / "include/linux/jni_md.h",
  c.project / "lakefile.toml", c.project / "native/app_jni.cpp",
  c.project / "native/include/kotlean_jni.hpp", c.project / "host/wire/src/test/cpp/app_exports.map",
  c.project / "host/wire/src/test/cpp/app_memory.cpp", c.source
]

def commands (c : Config) : Array Command := #[
  ⟨(c.toolchain / "bin/lake").toString, #["build", "Kotlean:static", "Kotlean.Export"], c.project⟩,
  ⟨(c.toolchain / "bin/lake").toString,
    #["env", "lean", "--root=" ++ (c.source.parent.getD ".").toString,
      "-c", c.output.toString ++ ".gen.c", c.source.toString], c.project⟩,
  ⟨"c++", #["-c", "-fPIC", "-std=c++17", "-fno-exceptions", "-fno-rtti",
    "-DKOTLEAN_INITIALIZER=" ++ c.initializer,
    "-I" ++ (c.toolchain / "include").toString,
    "-I" ++ (c.jdk / "include").toString, "-I" ++ (c.jdk / "include/linux").toString,
    "-I" ++ (c.project / "native/include").toString,
    (c.project / "native/app_jni.cpp").toString,
    "-o", c.output.toString ++ ".jni.o"], c.project⟩,
  ⟨"c++", #["-c", "-fPIC", "-std=c++17", "-fno-exceptions", "-fno-rtti",
    "-I" ++ (c.toolchain / "include").toString,
    "-I" ++ (c.jdk / "include").toString, "-I" ++ (c.jdk / "include/linux").toString,
    "-I" ++ (c.project / "native/include").toString,
    (c.project / "host/wire/src/test/cpp/app_memory.cpp").toString,
    "-o", c.output.toString ++ ".probe.o"], c.project⟩,
  ⟨(c.toolchain / "bin/leanc").toString,
    #["-c", "-fPIC", "-ffunction-sections", "-fdata-sections", c.output.toString ++ ".gen.c",
      "-o", c.output.toString ++ ".app.o"], c.project⟩,
  ⟨(c.toolchain / "bin/leanc").toString,
    #["-shared", "-fPIC", c.output.toString ++ ".jni.o", c.output.toString ++ ".app.o",
      c.output.toString ++ ".probe.o",
      "-Wl,-z,defs", "-Wl,--gc-sections",
      "-Wl,--version-script=" ++ (c.project / "host/wire/src/test/cpp/app_exports.map").toString,
      (c.project / ".lake/build/lib/libkotlean_Kotlean.a").toString,
      "-L" ++ (c.toolchain / "lib/lean").toString, "-lleanshared",
      "-Wl,-rpath," ++ (c.toolchain / "lib/lean").toString,
      "-o", c.output.toString ++ ".tmp"], c.project⟩
]

def prepare (missing : List System.FilePath) (c : Config) : Except String (Array Command) :=
  match missing with
  | [] => .ok (commands c)
  | first :: _ => .error s!"Missing build prerequisite: {first}"

theorem ready_plan (c : Config) : prepare [] c = .ok (commands c) := rfl
theorem missing_refuses (first : System.FilePath) (rest : List System.FilePath) (c : Config) :
    prepare (first :: rest) c = .error s!"Missing build prerequisite: {first}" := rfl

end BuildAppNative

def main (args : List String) : IO Unit := do
  let [project, toolchain, jdk, source, initializer, output] := args
    | throw (IO.userError "Usage: lean --run tools/BuildAppNative.lean PROJECT TOOLCHAIN JDK APP_LEAN RUNTIME_INITIALIZER OUTPUT")
  let base ← IO.currentDir
  let config : BuildAppNative.Config :=
    ⟨base / project, base / toolchain, base / jdk, base / source, initializer, base / output⟩
  let mut missing := []
  for path in BuildAppNative.requirements config do
    unless ← path.pathExists do missing := missing ++ [path]
  let .ok commands := BuildAppNative.prepare missing config
    | throw (IO.userError s!"Missing build prerequisites: {missing}")
  IO.FS.createDirAll (config.output.parent.getD ".")
  for command in commands do
    IO.println s!"Running {command.executable} {String.intercalate " " command.arguments.toList}"
    let result ← IO.Process.output {
      cmd := command.executable, args := command.arguments, cwd := some command.directory }
    IO.print result.stdout
    IO.eprint result.stderr
    if result.exitCode != 0 then throw (IO.userError s!"Native build failed with exit {result.exitCode}")
  IO.FS.rename (config.output.toString ++ ".tmp") config.output
  IO.println s!"Native app library: {config.output}"
