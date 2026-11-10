import Kotlean.Wire.Adapt
import Kotlean.Wire.Basic
import Kotlean.Wire.List

namespace Kotlean.Wire

def zigzag : Int → Nat
  | .ofNat value => 2 * value
  | .negSucc value => 2 * value + 1

def unzigzag (value : Nat) : Int :=
  if value % 2 = 0 then .ofNat (value / 2) else .negSucc (value / 2)

theorem unzigzag_zigzag (value : Int) : unzigzag (zigzag value) = value := by
  cases value <;> simp [zigzag, unzigzag] <;> omega

theorem zigzag_unzigzag (value : Nat) : zigzag (unzigzag value) = value := by
  unfold unzigzag
  split
  · simp only [zigzag]
    omega
  · simp only [zigzag]
    omega

def signed : Codec Int := adapt natural zigzag (some ∘ unzigzag)
  (by intro value; simp [unzigzag_zigzag])
  (by
    intro raw value accepted
    simp only [Function.comp_apply, Option.some.injEq] at accepted
    subst value
    exact zigzag_unzigzag raw)

def colorProject (value : Nat) : Option UInt32 :=
  if value < 2 ^ 32 then some (UInt32.ofNat value) else none

theorem colorProject_toNat (value : UInt32) : colorProject value.toNat = some value := by
  have bound := UInt32.toNat_lt value
  simp [colorProject, bound]

theorem colorProject_sound (raw : Nat) (value : UInt32)
    (accepted : colorProject raw = some value) : value.toNat = raw := by
  unfold colorProject at accepted
  split at accepted
  · rename_i bound
    cases accepted
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt bound]
  · cases accepted

def color : Codec UInt32 := adapt natural UInt32.toNat colorProject
  colorProject_toNat colorProject_sound

def utf8Bytes (value : String) : List UInt8 := value.toUTF8.data.toList

def utf8Project (value : List UInt8) : Option String :=
  String.fromUTF8? ⟨value.toArray⟩

theorem utf8Project_bytes (value : String) : utf8Project (utf8Bytes value) = some value := by
  cases value with
  | ofByteArray bytes valid =>
    simp [utf8Project, utf8Bytes, String.fromUTF8?, String.fromUTF8, valid]

theorem utf8Project_sound (raw : List UInt8) (value : String)
    (accepted : utf8Project raw = some value) : utf8Bytes value = raw := by
  unfold utf8Project String.fromUTF8? at accepted
  split at accepted
  · cases accepted
    simp [utf8Bytes, String.fromUTF8]
  · cases accepted

def text : Codec String := adapt (list byte) utf8Bytes utf8Project
  utf8Project_bytes utf8Project_sound

end Kotlean.Wire
