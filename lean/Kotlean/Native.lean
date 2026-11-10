module
public import Kotlean.Runtime.Engine
public import Kotlean.Wire.Output

@[expose] public section

namespace Kotlean.Native

abbrev Packet (app : App) := Option (Runtime.State app) × ByteArray

def start (app : App) (bytes : ByteArray) : Packet app :=
  match Wire.decodeBytes Wire.initInput bytes with
  | none => (none, Wire.encodeBytes Wire.out (.failed "Malformed initialization packet"))
  | some input =>
    let result := Runtime.start app input
    (some result.1, Wire.encodeBytes Wire.out result.2)

def step (app : App) (state : Option (Runtime.State app)) (bytes : ByteArray) : Packet app :=
  match state with
  | none => (none, Wire.encodeBytes Wire.out (.ignored none))
  | some state =>
    match Wire.decodeBytes Wire.event bytes with
    | none => (some state, Wire.encodeBytes Wire.out (.ignored (some "Malformed event packet")))
    | some event =>
      let result := Runtime.step event state
      (some result.1, Wire.encodeBytes Wire.out result.2)

theorem start_valid (app : App) (bytes : ByteArray) (input : InitInput)
    (accepted : Wire.decodeBytes Wire.initInput bytes = some input) :
    start app bytes =
      let result := Runtime.start app input
      (some result.1, Wire.encodeBytes Wire.out result.2) := by
  simp [start, accepted]

theorem start_invalid (app : App) (bytes : ByteArray)
    (rejected : Wire.decodeBytes Wire.initInput bytes = none) :
    start app bytes = (none, Wire.encodeBytes Wire.out (.failed "Malformed initialization packet")) := by
  simp [start, rejected]

theorem step_valid (app : App) (state : Runtime.State app) (bytes : ByteArray) (event : Event)
    (accepted : Wire.decodeBytes Wire.event bytes = some event) :
    step app (some state) bytes =
      let result := Runtime.step event state
      (some result.1, Wire.encodeBytes Wire.out result.2) := by
  simp [step, accepted]

theorem step_invalid (app : App) (state : Runtime.State app) (bytes : ByteArray)
    (rejected : Wire.decodeBytes Wire.event bytes = none) :
    step app (some state) bytes =
      (some state, Wire.encodeBytes Wire.out (.ignored (some "Malformed event packet"))) := by
  simp [step, rejected]

theorem step_freed (app : App) (bytes : ByteArray) :
    step app none bytes = (none, Wire.encodeBytes Wire.out (.ignored none)) := rfl

theorem start_canonical (app : App) (bytes : ByteArray) :
    ∃ output, (start app bytes).2 = Wire.encodeBytes Wire.out output := by
  cases decoded : Wire.decodeBytes Wire.initInput bytes with
  | none => exact ⟨.failed "Malformed initialization packet", by simp [start, decoded]⟩
  | some input => exact ⟨(Runtime.start app input).2, by simp [start, decoded]⟩

theorem step_canonical (app : App) (state : Option (Runtime.State app)) (bytes : ByteArray) :
    ∃ output, (step app state bytes).2 = Wire.encodeBytes Wire.out output := by
  cases state with
  | none => exact ⟨.ignored none, rfl⟩
  | some state =>
    cases decoded : Wire.decodeBytes Wire.event bytes with
    | none => exact ⟨.ignored (some "Malformed event packet"), by simp [step, decoded]⟩
    | some event => exact ⟨(Runtime.step event state).2, by simp [step, decoded]⟩

end Kotlean.Native
