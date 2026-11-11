module
import Kotlean
meta import Kotlean.Export

open Kotlean

inductive Msg where
  | run
  | result (name : String) (ok : Bool)
  | tick
  | back
  | pause
  | resume

structure Model where
  report : List String := []
  ticking : Bool := true
  listensBack : Bool := true

def mark (name : String) (verify : Reply → Bool) (effect : Effect) : Cmd Msg :=
  ⟨effect, some fun reply => some (.result name (verify reply))⟩

def ok : Reply → Bool
  | .ok _ => true
  | .error _ => false

def failed : Reply → Bool
  | .ok _ => false
  | .error _ => true

def hasBytes (expected : List UInt8) : Reply → Bool
  | .ok actual => actual == expected
  | .error _ => false

def commands : List (Cmd Msg) :=
  [mark "write" ok (.write "host-fixture" [0, 7, 255]),
   mark "read" (hasBytes [0, 7, 255]) (.read "host-fixture"),
   mark "log" ok (.log "Kotlean host fixture log"),
   mark "haptic" ok .haptic,
   mark "clipboard" ok (.clipboard "Kotlean-clipboard-fixture"),
   mark "clipboard-observed" (hasBytes [1]) (.platform "clipboard-check" []),
   mark "worker" (hasBytes [2, 9]) (.platform "worker" [9, 2]),
   mark "missing" failed (.platform "missing" []),
   mark "delay" ok (.delay 500)]

def update (msg : Msg) (model : Model) : Model × List (Cmd Msg) :=
  let append (label : String) := { model with report := model.report ++ [label] }
  match msg with
  | .run => (model, commands)
  | .result name passed => (append (name ++ if passed then "=ok" else "=error"), [])
  | .tick => ({ append "tick" with ticking := false }, [])
  | .back => ({ append "back" with listensBack := false }, [])
  | .pause => (append "pause", [])
  | .resume => (append "resume", [])

def subscriptions (model : Model) : List (Kotlean.Sub Msg) :=
  [⟨.pause, fun _ => some .pause⟩, ⟨.resume, fun _ => some .resume⟩] ++
  (if model.ticking then [⟨.tick 150, fun _ => some .tick⟩] else []) ++
  (if model.listensBack then [⟨.back, fun _ => some .back⟩] else [])

def app : App := {
  Model := Model
  Msg := Msg
  init := ({}, [])
  update := update
  view := fun model => .button {
    text := String.intercalate "," ("Effects" :: model.report)
    events := { click := some .run }
  }
  subscriptions := subscriptions
}

kotlean_app app
