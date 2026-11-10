module
public import KotleanBuild.Contracts
public import KotleanBuild.Policy

@[expose] public section

namespace KotleanBuild.Verified
open KotleanBuild.Contracts

theorem missing : preflightMissing KotleanBuild.preflight := by
  intro first rest commands
  rfl

theorem ready : preflightReady KotleanBuild.preflight := by
  intro commands
  rfl

theorem cache : cacheContract KotleanBuild.cacheHit := by
  intro signature expected cached observed
  cases cached with
  | none => simp [KotleanBuild.cacheHit]
  | some entry =>
    simp [KotleanBuild.cacheHit, artifactsMatch, Bool.and_eq_true, List.all_eq_true,
      and_assoc]
    intros
    exact eq_comm

theorem dedup_nodup (values : List String) : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp
    · exact dedup_nodup _
termination_by values.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem libc : clashesContract KotleanBuild.clashes := by
  intro defined libc
  constructor
  · exact dedup_nodup _
  · intro name
    simp [KotleanBuild.clashes]

theorem collected (expected : List String) (observed : Observations) (artifacts : List KotleanBuild.Artifact) :
    KotleanBuild.collectArtifacts expected observed = some artifacts ↔
      artifacts.map (fun artifact => artifact.path) = expected ∧
        ∀ artifact ∈ artifacts, observed.lookup artifact.path = some (some artifact.digest) := by
  induction expected generalizing artifacts with
  | nil =>
    cases artifacts <;> simp [KotleanBuild.collectArtifacts]
  | cons path rest ih =>
    constructor
    · intro accepted
      cases lookupEq : observed.lookup path with
      | none => simp [KotleanBuild.collectArtifacts, lookupEq] at accepted
      | some optionDigest =>
        cases optionDigest with
        | none => simp [KotleanBuild.collectArtifacts, lookupEq] at accepted
        | some digest =>
          cases tailEq : KotleanBuild.collectArtifacts rest observed with
          | none => simp [KotleanBuild.collectArtifacts, lookupEq, tailEq] at accepted
          | some tail =>
            simp only [KotleanBuild.collectArtifacts, lookupEq, tailEq, Option.some.injEq] at accepted
            subst artifacts
            have tailGood := (ih tail).mp tailEq
            simp only [List.map_cons, tailGood.1, List.mem_cons,
              forall_eq_or_imp, lookupEq, true_and]
            exact tailGood.2
    · rintro ⟨names, values⟩
      cases artifacts with
      | nil => cases names
      | cons artifact tail =>
        have headEq : artifact.path = path := (List.cons.inj names).1
        have tailEq : tail.map (fun artifact => artifact.path) = rest := (List.cons.inj names).2
        have headRead := values artifact (by simp)
        rw [headEq] at headRead
        have tailRead : ∀ value ∈ tail, observed.lookup value.path = some (some value.digest) :=
          fun value member => values value (by simp [member])
        have acceptedTail := (ih tail).mpr ⟨tailEq, tailRead⟩
        cases artifact
        simp_all [KotleanBuild.collectArtifacts]

theorem completion : sealContract KotleanBuild.finishCache := by
  intro signature expected required results observed entry
  simp only [artifactsMatch]
  rw [← collected expected observed entry.artifacts]
  cases entry with
  | mk stored complete artifacts =>
    cases collectedEq : KotleanBuild.collectArtifacts expected observed with
    | none => simp [KotleanBuild.finishCache, collectedEq]
    | some found =>
      simp [KotleanBuild.finishCache, collectedEq, finishedSteps, List.all_eq_true,
        Bool.and_eq_true, Bool.or_eq_true, and_assoc]
      grind

end KotleanBuild.Verified
