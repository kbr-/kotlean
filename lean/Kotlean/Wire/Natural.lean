import Kotlean.Wire.Codec

namespace Kotlean.Wire

def writeNatural (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else UInt8.ofNat (value % 128 + 128) :: writeNatural (value / 128)
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private def readNaturalRaw : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | head :: tail =>
    if head.toNat < 128 then some (head.toNat, tail)
    else do
      let (high, rest) ← readNaturalRaw tail
      pure (head.toNat - 128 + 128 * high, rest)

private def readNatural (input : List UInt8) : Option (Nat × List UInt8) := do
  let (value, rest) ← readNaturalRaw input
  if input = writeNatural value ++ rest then some (value, rest) else none

private theorem readNaturalRaw_write (value : Nat) (tail : List UInt8) :
    readNaturalRaw (writeNatural value ++ tail) = some (value, tail) := by
  induction value using Nat.strongRecOn generalizing tail with
  | ind value ih =>
    rw [writeNatural]
    split
    next small =>
      have byteValue : (UInt8.ofNat value).toNat = value := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      rw [List.cons_append, readNaturalRaw, byteValue, ite_eq_left small]
      rfl
    next large =>
      have lowBound := Nat.mod_lt value (by decide : 0 < 128)
      have byteValue : (UInt8.ofNat (value % 128 + 128)).toNat =
          value % 128 + 128 := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have continued : ¬ value % 128 + 128 < 128 := by omega
      have low : value % 128 + 128 - 128 = value % 128 := by omega
      rw [List.cons_append, readNaturalRaw, byteValue, ite_eq_right continued,
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
        exact canonical
      · cases h
  positive := by
    intro value
    rw [writeNatural]
    split <;> exact Nat.zero_lt_succ _

theorem natural_small (value : Nat) (small : value < 128) :
    natural.write value = [UInt8.ofNat value] := by
  change writeNatural value = _
  rw [writeNatural, ite_eq_left small]

theorem natural_large (value : Nat) (large : 128 ≤ value) :
    natural.write value = UInt8.ofNat (value % 128 + 128) ::
      natural.write (value / 128) := by
  change writeNatural value = _
  rw [writeNatural, ite_eq_right (by omega : ¬ value < 128)]
  rfl

end Kotlean.Wire
