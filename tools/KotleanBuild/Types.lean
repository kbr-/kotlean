module
public import Lean

@[expose] public section
namespace KotleanBuild

inductive Abi where
  | linuxX86_64
  | androidArm64
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Lean.ToJson, Lean.FromJson

structure Artifact where
  path : String
  digest : String
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Lean.ToJson, Lean.FromJson

structure Signature where
  format : Nat
  toolchain : String
  abi : Abi
  ndk : String
  libuv : String
  flags : List String
  inputs : List Artifact
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Lean.ToJson, Lean.FromJson

structure Manifest where
  signature : Signature
  complete : Bool
  artifacts : List Artifact
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Lean.ToJson, Lean.FromJson

abbrev Observations := List (String × Option String)

end KotleanBuild
