import Kotlean.Wire.Codec

namespace Kotlean.Wire

private def writeNaturalReference (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else UInt8.ofNat (value % 128 + 128) :: writeNaturalReference (value / 128)
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private def writeNaturalAcc (value : Nat) (accumulator : List UInt8) : List UInt8 :=
  if value < 128 then (UInt8.ofNat value :: accumulator).reverse
  else writeNaturalAcc (value / 128) (UInt8.ofNat (value % 128 + 128) :: accumulator)
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private theorem writeNaturalAcc_agrees (value : Nat) (accumulator : List UInt8) :
    writeNaturalAcc value accumulator = accumulator.reverse ++ writeNaturalReference value := by
  induction value using Nat.strongRecOn generalizing accumulator with
  | ind value ih =>
    by_cases small : value < 128
    · simp [writeNaturalAcc, writeNaturalReference, small]
    · rw [writeNaturalAcc, ite_eq_right small]
      rw [writeNaturalReference, ite_eq_right small]
      rw [ih (value / 128) (Nat.div_lt_self (by omega) (by decide))]
      simp [List.reverse_cons, List.append_assoc]

def writeNatural (value : Nat) : List UInt8 := writeNaturalAcc value []

private theorem writeNatural_eq_reference (value : Nat) :
    writeNatural value = writeNaturalReference value := by
  simpa [writeNatural] using writeNaturalAcc_agrees value []

theorem writeNatural_unfold (value : Nat) :
    writeNatural value = if value < 128 then [UInt8.ofNat value]
      else UInt8.ofNat (value % 128 + 128) :: writeNatural (value / 128) := by
  simp only [writeNatural_eq_reference]
  rw [writeNaturalReference]

private def readNaturalRawReference : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | head :: tail =>
    if head.toNat < 128 then some (head.toNat, tail)
    else do
      let (high, rest) ← readNaturalRawReference tail
      pure (head.toNat - 128 + 128 * high, rest)

private def readNaturalAcc (accumulator multiplier : Nat) :
    List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | head :: tail =>
    if head.toNat < 128 then some (accumulator + multiplier * head.toNat, tail)
    else readNaturalAcc (accumulator + multiplier * (head.toNat - 128)) (multiplier * 128) tail

private theorem readNaturalAcc_agrees (input : List UInt8) (accumulator multiplier : Nat) :
    readNaturalAcc accumulator multiplier input =
      (readNaturalRawReference input).map (fun (value, rest) => (accumulator + multiplier * value, rest)) := by
  induction input generalizing accumulator multiplier with
  | nil => rfl
  | cons head tail ih =>
    by_cases small : head.toNat < 128
    · simp [readNaturalAcc, readNaturalRawReference, small]
    · simp only [readNaturalAcc, readNaturalRawReference, small, ite_false, ih]
      cases remaining : readNaturalRawReference tail with
      | none => simp
      | some result =>
        rcases result with ⟨value, rest⟩
        simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private def readNaturalRaw (input : List UInt8) : Option (Nat × List UInt8) :=
  readNaturalAcc 0 1 input

private theorem readNaturalRaw_eq_reference (input : List UInt8) :
    readNaturalRaw input = readNaturalRawReference input := by
  simpa [readNaturalRaw] using readNaturalAcc_agrees input 0 1

private theorem readNaturalRaw_unfold (input : List UInt8) :
    readNaturalRaw input = (match input with
      | [] => none
      | head :: tail =>
        if head.toNat < 128 then some (head.toNat, tail)
        else do
          let (high, rest) ← readNaturalRaw tail
          pure (head.toNat - 128 + 128 * high, rest)) := by
  simp only [readNaturalRaw_eq_reference]
  cases input <;> rfl

private def readNatural (input : List UInt8) : Option (Nat × List UInt8) := do
  let (value, rest) ← readNaturalRaw input
  if equal input (writeNatural value ++ rest) then some (value, rest) else none

private theorem readNaturalRaw_write (value : Nat) (tail : List UInt8) :
    readNaturalRaw (writeNatural value ++ tail) = some (value, tail) := by
  induction value using Nat.strongRecOn generalizing tail with
  | ind value ih =>
    rw [writeNatural_unfold]
    split
    next small =>
      have byteValue : (UInt8.ofNat value).toNat = value := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      rw [List.cons_append, readNaturalRaw_unfold]
      dsimp only
      rw [byteValue, ite_eq_left small]
      rfl
    next large =>
      have lowBound := Nat.mod_lt value (by decide : 0 < 128)
      have byteValue : (UInt8.ofNat (value % 128 + 128)).toNat =
          value % 128 + 128 := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have continued : ¬ value % 128 + 128 < 128 := by omega
      have low : value % 128 + 128 - 128 = value % 128 := by omega
      rw [List.cons_append, readNaturalRaw_unfold]
      dsimp only
      rw [byteValue, ite_eq_right continued,
        ih (value / 128) (Nat.div_lt_self (by omega) (by decide))]
      change some (value % 128 + 128 - 128 + 128 * (value / 128), tail) = _
      rw [low, Nat.mod_add_div]

def natural : Codec Nat where
  write := writeNatural
  read := readNatural
  roundTrip := by
    intro value tail
    simp [readNatural, readNaturalRaw_write]
  sound := by
    intro input value rest h
    cases parsed : readNaturalRaw input with
    | none => simp [readNatural, parsed] at h
    | some result =>
      rcases result with ⟨item, tail⟩
      simp only [readNatural, parsed, bind, Option.bind] at h
      split at h
      · rename_i canonical
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact (equal_true _ _).mp canonical
      · cases h
  positive := by
    intro value
    rw [writeNatural_unfold]
    split <;> exact Nat.zero_lt_succ _

theorem natural_small (value : Nat) (small : value < 128) :
    natural.write value = [UInt8.ofNat value] := by
  change writeNatural value = _
  rw [writeNatural_unfold, ite_eq_left small]

theorem natural_large (value : Nat) (large : 128 ≤ value) :
    natural.write value = UInt8.ofNat (value % 128 + 128) ::
      natural.write (value / 128) := by
  change writeNatural value = _
  rw [writeNatural_unfold, ite_eq_right (by omega : ¬ value < 128)]
  rfl

end Kotlean.Wire
