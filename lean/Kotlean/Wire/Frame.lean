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

def encodeBytes (codec : Codec α) (value : α) : ByteArray :=
  ⟨(codec.write value).toArray⟩

def decodeBytes (codec : Codec α) (input : ByteArray) : Option α :=
  decode codec input.data.toList

theorem decodeBytes_encodeBytes (codec : Codec α) (value : α) :
    decodeBytes codec (encodeBytes codec value) = some value := by
  simp [encodeBytes, decodeBytes, decode_write]

theorem decodeBytes_exact (codec : Codec α) (input : ByteArray) (value : α) :
    decodeBytes codec input = some value ↔ encodeBytes codec value = input := by
  change decode codec input.data.toList = some value ↔ _
  rw [decode_exact]
  constructor
  · intro exactBytes
    have := congrArg (fun bytes : List UInt8 => (ByteArray.mk bytes.toArray)) exactBytes
    cases input
    simpa [encodeBytes] using this
  · intro exactArray
    have := congrArg (fun bytes : ByteArray => bytes.data.toList) exactArray
    simpa [encodeBytes] using this

end Kotlean.Wire
