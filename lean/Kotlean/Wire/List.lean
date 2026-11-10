module
public import Kotlean.Wire.Natural

@[expose] public section

namespace Kotlean.Wire

def readMany (element : Codec α) : Nat → List UInt8 →
    Option (List α × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
    let (value, tail) ← element.read input
    let (values, rest) ← readMany element count tail
    pure (value :: values, rest)

def readManyAcc (element : Codec α) : Nat → List UInt8 → List α →
    Option (List α × List UInt8)
  | 0, input, accumulator => some (accumulator.reverse, input)
  | count + 1, input, accumulator => do
    let (value, tail) ← element.read input
    readManyAcc element count tail (value :: accumulator)

private theorem readManyAcc_agrees (element : Codec α) (count : Nat)
    (input : List UInt8) (accumulator : List α) :
    readManyAcc element count input accumulator =
      (readMany element count input).map (fun (values, rest) => (accumulator.reverse ++ values, rest)) := by
  induction count generalizing input accumulator with
  | zero => simp [readManyAcc, readMany]
  | succ count ih =>
    cases first : element.read input with
    | none => simp [readManyAcc, readMany, first]
    | some result =>
      rcases result with ⟨value, tail⟩
      simp only [readManyAcc, readMany, first, bind, Option.bind, ih]
      cases remaining : readMany element count tail with
      | none => simp
      | some result =>
        rcases result with ⟨values, rest⟩
        simp [List.reverse_cons, List.append_assoc]

private theorem readMany_write (element : Codec α) (values : List α)
    (tail : List UInt8) :
    readMany element values.length (values.flatMap element.write ++ tail) =
      some (values, tail) := by
  induction values generalizing tail with
  | nil => rfl
  | cons value values ih =>
    simp [readMany, List.append_assoc, element.roundTrip, ih]

private theorem readMany_sound (element : Codec α) (count : Nat)
    (input : List UInt8) (values : List α) (rest : List UInt8)
    (accepted : readMany element count input = some (values, rest)) :
    input = values.flatMap element.write ++ rest ∧ values.length = count := by
  induction count generalizing input values rest with
  | zero =>
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | succ count ih =>
    cases first : element.read input with
    | none => simp [readMany, first] at accepted
    | some firstResult =>
      rcases firstResult with ⟨value, tail⟩
      cases remaining : readMany element count tail with
      | none => simp [readMany, first, remaining] at accepted
      | some remainingResult =>
        rcases remainingResult with ⟨items, remainder⟩
        simp [readMany, first, remaining] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        rcases ih tail items remainder remaining with ⟨tailSound, lengthSound⟩
        constructor
        · rw [element.sound input value tail first, tailSound]
          simp [List.append_assoc]
        · simp [lengthSound]

private theorem writeMany_length (element : Codec α) (values : List α) :
    values.length ≤ (values.flatMap element.write).length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons value values ih =>
    have positive := element.positive value
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

def readList (element : Codec α) (input : List UInt8) :
    Option (List α × List UInt8) := do
  let (count, tail) ← natural.read input
  if count ≤ tail.length then readManyAcc element count tail [] else none

def list (element : Codec α) : Codec (List α) where
  write values := natural.write values.length ++ values.flatMap element.write
  read := readList element
  roundTrip := by
    intro values tail
    have bound : values.length ≤ (values.flatMap element.write ++ tail).length := by
      have := writeMany_length element values
      simp only [List.length_append]
      omega
    simp only [readList, List.append_assoc, natural.roundTrip, bind, Option.bind]
    rw [ite_eq_left bound]
    rw [readManyAcc_agrees]
    simp only [List.reverse_nil, List.nil_append]
    simpa using readMany_write element values tail
  sound := by
    intro input values rest accepted
    cases first : natural.read input with
    | none => simp [readList, first] at accepted
    | some firstResult =>
      rcases firstResult with ⟨count, tail⟩
      simp only [readList, first, bind, Option.bind] at accepted
      split at accepted
      · rw [readManyAcc_agrees] at accepted
        simp only [List.reverse_nil, List.nil_append] at accepted
        rcases readMany_sound element count tail values rest (by simpa using accepted) with
          ⟨tailSound, lengthSound⟩
        rw [natural.sound input count tail first, tailSound, ← lengthSound]
        exact (List.append_assoc _ _ _).symm
      · cases accepted
  positive := by
    intro values
    have positive := natural.positive values.length
    simp only [List.length_append]
    omega

end Kotlean.Wire
