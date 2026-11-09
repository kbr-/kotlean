import Kotlean.Wire.Codec

namespace Kotlean.Wire

def decode (codec : Codec α) (input : List UInt8) : Option α :=
  match codec.read input with
  | some (value, []) => some value
  | _ => none

theorem decode_write (codec : Codec α) (value : α) :
    decode codec (codec.write value) = some value := by
  have h : codec.read (codec.write value) = some (value, []) := by
    simpa using codec.roundTrip value []
  simp [decode, h]

theorem decode_exact (codec : Codec α) (input : List UInt8) (value : α) :
    decode codec input = some value ↔ codec.write value = input := by
  constructor
  · intro h
    cases parsed : codec.read input with
    | none => simp [decode, parsed] at h
    | some result =>
      rcases result with ⟨item, rest⟩
      cases rest with
      | nil =>
        simp [decode, parsed] at h
        subst item
        simpa using (codec.sound input value [] parsed).symm
      | cons head tail => simp [decode, parsed] at h
  · intro h
    subst input
    exact decode_write codec value

end Kotlean.Wire
