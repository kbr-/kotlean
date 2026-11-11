module
import Kotlean
meta import Kotlean.Export

open Kotlean

inductive Msg where
  | close | unexpectedTimer

def app : App := {
  Model := Bool
  Msg := Msg
  init := (false, [])
  update := fun message _ => match message with
    | .close => (false, [⟨.platform "stop" [], none⟩, ⟨.write "after-close" [1], none⟩])
    | .unexpectedTimer => (true, [])
  view := fun fired => .column {}
    [ .input { text := "fixed" }
    , .button {
        text := if fired then "Timer fired unexpectedly" else "Close host"
        events := { click := some .close } } ]
  subscriptions := fun _ => [⟨.tick 9223372036854775807, fun _ => some .unexpectedTimer⟩]
}

kotlean_app app
