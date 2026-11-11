module
import Kotlean
meta import Kotlean.Export

open Kotlean

inductive Msg where
  | close | touched (frame : TouchFrame) | unexpectedTimer | key

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
    | .key => (model, [])
  view := fun model =>
    let editor : Ui Msg := .input { text := "fixed" }
    let leading : List (Ui Msg) :=
      [ .canvas {
          width := .dp 90
          height := .dp 40
          description := "Keyboard probe"
          events := { key := some (fun _ _ => .key) } }
      , .input { text := "other" } ] ++
      if model.touched then [.column {} [], editor] else [.column {} [editor]]
    let controls : List (Ui Msg) :=
      [ .button {
          text := if model.fired then "Timer fired unexpectedly"
            else if model.touched then "Close host (touch observed)" else "Close host"
          events := { click := some .close, touch := some .touched } } ]
    .column {} (leading ++ controls)
  subscriptions := fun _ => [⟨.tick 9223372036854775807, fun _ => some .unexpectedTimer⟩]
}

kotlean_app app
