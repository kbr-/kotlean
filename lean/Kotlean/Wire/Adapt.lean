import Kotlean.Wire.Codec

namespace Kotlean.Wire

private def readAdapt (base : Codec α) (project : α → Option β)
    (input : List UInt8) : Option (β × List UInt8) := do
  let (raw, tail) ← base.read input
  let value ← project raw
  pure (value, tail)

def adapt (base : Codec α) (embed : β → α) (project : α → Option β)
    (projectEmbed : ∀ value, project (embed value) = some value)
    (embedProject : ∀ raw value, project raw = some value → embed value = raw) : Codec β where
  write value := base.write (embed value)
  read := readAdapt base project
  roundTrip := by
    intro value tail
    simp [readAdapt, base.roundTrip, projectEmbed]
  sound := by
    intro input value rest accepted
    cases first : base.read input with
    | none => simp [readAdapt, first] at accepted
    | some result =>
      rcases result with ⟨raw, tail⟩
      cases projected : project raw with
      | none => simp [readAdapt, first, projected] at accepted
      | some item =>
        simp [readAdapt, first, projected] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        rw [base.sound input raw tail first, embedProject raw item projected]
  positive := by
    intro value
    exact base.positive (embed value)

end Kotlean.Wire
