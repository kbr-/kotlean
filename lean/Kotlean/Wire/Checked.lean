import Kotlean.Wire.Adapt

namespace Kotlean.Wire

def checkedProject [BEq α] (embed : β → α) (project : α → Option β)
    (raw : α) : Option β := do
  let value ← project raw
  if equal (embed value) raw then some value else none

theorem checkedProject_embed [BEq α] [LawfulBEq α] (embed : β → α) (project : α → Option β)
    (inverse : ∀ value, project (embed value) = some value) (value : β) :
    checkedProject embed project (embed value) = some value := by
  simp [checkedProject, inverse]

theorem checkedProject_sound [BEq α] [LawfulBEq α] (embed : β → α) (project : α → Option β)
    (raw : α) (value : β) (accepted : checkedProject embed project raw = some value) :
    embed value = raw := by
  unfold checkedProject at accepted
  cases parsed : project raw with
  | none => simp [parsed] at accepted
  | some item =>
    simp only [parsed, bind, Option.bind] at accepted
    split at accepted
    · rename_i canonical
      cases accepted
      exact (equal_true _ _).mp canonical
    · cases accepted

def checked [BEq α] [LawfulBEq α] (base : Codec α) (embed : β → α) (project : α → Option β)
    (inverse : ∀ value, project (embed value) = some value) : Codec β :=
  adapt base embed (checkedProject embed project)
    (checkedProject_embed embed project inverse) (checkedProject_sound embed project)

end Kotlean.Wire
