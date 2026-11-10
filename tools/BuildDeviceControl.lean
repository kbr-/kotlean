import Std

def main (args : List String) : IO Unit := do
  let [project, jdk, sdk, stdlib, output] := args
    | throw (IO.userError "Usage: lean --run tools/BuildDeviceControl.lean PROJECT JDK SDK KOTLIN_STDLIB OUTPUT")
  let base ← IO.currentDir
  let project := base / project
  let jdk := base / jdk
  let sdk := base / sdk
  let stdlib := base / stdlib
  let output := base / output
  IO.FS.createDirAll output
  let jar := output / "control.jar"
  let sources := project / "host/wire/build/classes/kotlin"
  let archive ← IO.Process.output {
    cmd := (jdk / "bin/jar").toString
    args := #["--create", "--file", jar.toString, "-C", (sources / "main").toString, ".",
      "-C", (sources / "test").toString, "io/kotlean/AppControlKt.class"]}
  IO.print archive.stdout
  IO.eprint archive.stderr
  if archive.exitCode != 0 then throw (IO.userError "Cannot assemble the real JVM control classes")
  let dex ← IO.Process.output {
    cmd := (jdk / "bin/java").toString
    args := #["-XX:ActiveProcessorCount=4", "-cp", (sdk / "build-tools/37.0.0/lib/d8.jar").toString,
      "com.android.tools.r8.D8", "--min-api", "26", "--lib", (sdk / "platforms/android-37.0/android.jar").toString,
      "--output", (output / "control.zip").toString, jar.toString, stdlib.toString]}
  IO.print dex.stdout
  IO.eprint dex.stderr
  if dex.exitCode != 0 then throw (IO.userError "D8 rejected the control classes")
  IO.println s!"Device control dex: {output / "control.zip"}"
