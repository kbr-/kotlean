module
public import KotleanBuild.Types

@[expose] public section
namespace KotleanBuild

def cacheHit (signature : Signature) (expected : List String) (cached : Option Manifest)
    (observed : Observations) : Bool :=
  match cached with
  | none => false
  | some entry => entry.complete && signature == entry.signature && !expected.isEmpty &&
      entry.artifacts.map Artifact.path == expected &&
      entry.artifacts.all (fun artifact => observed.lookup artifact.path == some (some artifact.digest))

def preflight (missing commands : List String) : Except String (List String) :=
  match missing with
  | [] => .ok commands
  | first :: _ => .error s!"Missing prerequisite: {first}"

def clashes (defined libc : List String) : List String :=
  (defined.filter (fun name => libc.contains name)).eraseDups

def collectArtifacts : List String → Observations → Option (List Artifact)
  | [], _ => some []
  | path :: rest, observed =>
    match observed.lookup path with
    | some (some digest) =>
      match collectArtifacts rest observed with
      | some artifacts => some (⟨path, digest⟩ :: artifacts)
      | none => none
    | _ => none

def finishCache (signature : Signature) (expected required : List String)
    (results : List (String × UInt32)) (observed : Observations) : Option Manifest :=
  if expected.isEmpty || required.isEmpty then none
  else if decide required.Nodup && decide (results.map Prod.fst).Nodup &&
      decide ((results.map Prod.fst).Perm required) && results.all (fun result => result.2 == 0) then
    match collectArtifacts expected observed with
    | some artifacts => some ⟨signature, true, artifacts⟩
    | none => none
  else none

end KotleanBuild
