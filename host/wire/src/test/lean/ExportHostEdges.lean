module
import Kotlean
meta import Kotlean.Export

open Kotlean

inductive Msg where
  | close | touched (frame : TouchFrame) | unexpectedTimer

structure Model where
  fired : Bool := false
  touched : Bool := false

def app : App := {
  Model := Model
  Msg := Msg
  init := ({}, [])
  update := fun message model => match message with
    | .close => (model, [⟨.platform "stop" [], none⟩, ⟨.write "after-close" [1], none⟩])
    | .touched frame => ({ model with touched := model.touched || frame.phase == .down }, [])
    | .unexpectedTimer => ({ model with fired := true }, [])
  view := fun model => .column {}
    [ .input { text := "fixed" }
    , .button {
        text := if model.fired then "Timer fired unexpectedly"
          else if model.touched then "Close host (touch observed)" else "Close host"
        events := { click := some .close, touch := some .touched } } ]
  subscriptions := fun _ => [⟨.tick 9223372036854775807, fun _ => some .unexpectedTimer⟩]
}

kotlean_app app
