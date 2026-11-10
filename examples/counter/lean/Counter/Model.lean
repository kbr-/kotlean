module
public import Counter.View

@[expose] public section

namespace Counter
open Kotlean

abbrev Value := Nat × String
abbrev Model := Value × Bool

inductive Action where
  | increment | decrement | reset | edit (note : String)
  | delay | loaded (value : Option Value)

def transition (action : Action) (value : Value) (waiting : Bool) : Model :=
  match action with
  | .increment => ((value.1 + 1, value.2), false)
  | .decrement => ((value.1 - 1, value.2), false)
  | .reset => ((0, value.2), false)
  | .edit note => ((value.1, note), false)
  | .delay => (value, false)
  | .loaded stored => (if waiting then stored.getD value else value, false)

def codec : Wire.Codec Value := Wire.pair Wire.natural Wire.text
def save (model : Model) : List UInt8 := codec.write model.1
def restore (bytes : List UInt8) : Option Model :=
  (Wire.decode codec bytes).map (fun value => (value, false))

theorem restore_save (model : Model) : restore (save model) = some (model.1, false) := by
  simp [restore, save, Wire.decode_write]

def storedReply : Reply → Option Action
  | .ok bytes => some (.loaded (Wire.decode codec bytes))
  | .error _ => some (.loaded none)

def delayedReply : Reply → Option Action
  | .ok _ => some .increment
  | .error _ => none

def update (action : Action) (model : Model) : Model × List (Cmd Action) :=
  let next := transition action model.1 model.2
  let commands := match action with
    | .delay => [⟨.delay 500, some delayedReply⟩]
    | .loaded _ => []
    | _ => [⟨.write "counter" (save next), none⟩]
  (next, commands)

theorem delay_requests_increment (model : Model) (payload : List UInt8) :
    (update .delay model).2 =
      [⟨.delay 500, some delayedReply⟩] ∧ delayedReply (.ok payload) = some .increment :=
  ⟨rfl, rfl⟩

theorem failed_delay_has_no_message (message : String) : delayedReply (.error message) = none :=
  rfl

def appView (model : Model) : Ui Action :=
  .column { width := .fill, height := .fill, background := 0xff151928 }
    [ controls model.1.1 .increment .decrement .delay,
      .button { text := "Reset", padding := 16, events := { click := some .reset } },
      .input {
        text := model.1.2, hint := "Note", width := .fill, padding := 16
        background := 0xff292f46, events := { text := some .edit } } ]

def app : App := {
  Model := Model
  Msg := Action
  init := (((0, ""), true), [⟨.read "counter", some storedReply⟩])
  update := update
  view := appView
  persistence := some ⟨save, restore⟩
}

end Counter
