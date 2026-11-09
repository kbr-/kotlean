import Kotlean.Wire.Adapt

namespace Kotlean.Wire

def checkedProject [DecidableEq α] (embed : β → α) (project : α → Option β)
    (raw : α) : Option β := do
  let value ← project raw
  if embed value = raw then some value else none

theorem checkedProject_embed [DecidableEq α] (embed : β → α) (project : α → Option β)
    (inverse : ∀ value, project (embed value) = some value) (value : β) :
    checkedProject embed project (embed value) = some value := by
  simp [checkedProject, inverse]

theorem checkedProject_sound [DecidableEq α] (embed : β → α) (project : α → Option β)
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
      exact canonical
    · cases accepted

def checked [DecidableEq α] (base : Codec α) (embed : β → α) (project : α → Option β)
    (inverse : ∀ value, project (embed value) = some value) : Codec β :=
  adapt base embed (checkedProject embed project)
    (checkedProject_embed embed project inverse) (checkedProject_sound embed project)

end Kotlean.Wire
