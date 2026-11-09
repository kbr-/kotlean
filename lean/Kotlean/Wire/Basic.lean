import Kotlean.Wire.Codec

namespace Kotlean.Wire

def byte : Codec UInt8 where
  write value := [value]
  read
    | [] => none
    | value :: tail => some (value, tail)
  roundTrip := by intro value tail; rfl
  sound := by
    intro input value rest h
    cases input with
    | nil => cases h
    | cons byte tail =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  positive := by intro value; exact Nat.zero_lt_succ 0

private def readBool : List UInt8 → Option (Bool × List UInt8)
  | [] => none
  | value :: tail =>
    if value = 0 then some (false, tail)
    else if value = 1 then some (true, tail)
    else none

def boolean : Codec Bool where
  write value := [if value then 1 else 0]
  read := readBool
  roundTrip := by intro value tail; cases value <;> rfl
  sound := by
    intro input value rest h
    cases input with
    | nil => cases h
    | cons head tail =>
      simp only [readBool] at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · cases h
  positive := by intro value; exact Nat.zero_lt_succ 0

private def readPair (left : Codec α) (right : Codec β)
    (input : List UInt8) : Option ((α × β) × List UInt8) := do
  let (a, tail) ← left.read input
  let (b, rest) ← right.read tail
  pure ((a, b), rest)

def pair (left : Codec α) (right : Codec β) : Codec (α × β) where
  write value := left.write value.1 ++ right.write value.2
  read := readPair left right
  roundTrip := by
    intro value tail
    rcases value with ⟨a, b⟩
    simp [readPair, List.append_assoc, left.roundTrip, right.roundTrip]
  sound := by
    intro input value rest h
    cases first : left.read input with
    | none => simp [readPair, first] at h
    | some firstValue =>
      rcases firstValue with ⟨a, tail⟩
      cases second : right.read tail with
      | none => simp [readPair, first, second] at h
      | some secondValue =>
        rcases secondValue with ⟨b, remainder⟩
        simp [readPair, first, second] at h
        rcases h with ⟨rfl, rfl⟩
        rw [left.sound input a tail first, right.sound tail b remainder second]
        exact (List.append_assoc _ _ _).symm
  positive := by
    intro value
    have positive := left.positive value.1
    simpa only [List.length_append] using
      Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _)

end Kotlean.Wire
