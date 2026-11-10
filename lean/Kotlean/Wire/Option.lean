module
public import Kotlean.Wire.Basic

@[expose] public section

namespace Kotlean.Wire

def readOption (element : Codec α) : List UInt8 → Option (Option α × List UInt8)
  | [] => none
  | tag :: tail =>
    if tag = 0 then some (none, tail)
    else if tag = 1 then do
      let (value, rest) ← element.read tail
      pure (some value, rest)
    else none

def optional (element : Codec α) : Codec (Option α) where
  write
    | none => [0]
    | some value => 1 :: element.write value
  read := readOption element
  roundTrip := by
    intro value tail
    cases value with
    | none => rfl
    | some value => simp [readOption, element.roundTrip]
  sound := by
    intro input value rest h
    cases input with
    | nil => cases h
    | cons tag tail =>
      simp only [readOption] at h
      split at h
      · rename_i zero
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        subst tag
        rfl
      · split at h
        · rename_i zero one
          cases decoded : element.read tail with
          | none => simp [decoded] at h
          | some result =>
            rcases result with ⟨item, remainder⟩
            simp [decoded] at h
            rcases h with ⟨rfl, rfl⟩
            subst tag
            rw [element.sound tail item remainder decoded]
            rfl
        · cases h
  positive := by
    intro value
    cases value <;> exact Nat.zero_lt_succ _

end Kotlean.Wire
