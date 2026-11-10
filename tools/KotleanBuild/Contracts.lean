module
public import KotleanBuild.Types

@[expose] public section
namespace KotleanBuild.Contracts

abbrev Observations := List (String × Option String)
abbrev CacheHit := Signature → List String → Option Manifest → Observations → Bool
abbrev Preflight := List String → List String → Except String (List String)
abbrev Clashes := List String → List String → List String
abbrev Seal := Signature → List String → List String → List (String × UInt32) → Observations → Option Manifest

def artifactsMatch (expected : List String) (entry : Manifest) (observed : Observations) : Prop :=
  expected ≠ [] ∧ entry.artifacts.map (fun artifact => artifact.path) = expected ∧
    ∀ artifact ∈ entry.artifacts, observed.lookup artifact.path = some (some artifact.digest)

def cacheContract (hit : CacheHit) : Prop :=
  ∀ signature expected cached observed,
    hit signature expected cached observed = true ↔
      ∃ entry, cached = some entry ∧ entry.complete = true ∧ entry.signature = signature ∧
        artifactsMatch expected entry observed

def preflightMissing (prepare : Preflight) : Prop :=
  ∀ first rest commands, prepare (first :: rest) commands = .error s!"Missing prerequisite: {first}"

def preflightReady (prepare : Preflight) : Prop :=
  ∀ commands, prepare [] commands = .ok commands

def clashesContract (clashes : Clashes) : Prop :=
  ∀ defined libc,
    (clashes defined libc).Nodup ∧
      ∀ name, name ∈ clashes defined libc ↔ name ∈ defined ∧ name ∈ libc

def finishedSteps (required : List String) (results : List (String × UInt32)) : Prop :=
  required ≠ [] ∧ required.Nodup ∧ (results.map Prod.fst).Nodup ∧
    (results.map Prod.fst).Perm required ∧ ∀ result ∈ results, result.2 = 0

def sealContract (finish : Seal) : Prop :=
  ∀ signature expected required results observed entry,
    finish signature expected required results observed = some entry ↔
      entry.signature = signature ∧ entry.complete = true ∧
        artifactsMatch expected entry observed ∧ finishedSteps required results

end KotleanBuild.Contracts
