import Kotlean.Runtime.State
import Kotlean.Runtime.Contracts

namespace Kotlean.Runtime.Laws
open Kotlean

def effects : Out → List Effect
  | .changes output => output.commands.map Command.effect
  | _ => []

def commands : Out → List Command
  | .changes output => output.commands
  | _ => []

def patches : Out → List Patch
  | .changes output => output.patches
  | _ => []

def handlers (app : App) (state : Runtime.State app) : Contracts.Handlers app.Msg :=
  fun id => (state.rendered.handlers[id]?).map (fun handler => handler.dispatch)

def pending (app : App) (state : Runtime.State app) : Contracts.Pending (Option app.Msg) :=
  fun id => state.requests.pending[id]?

def edited (scene : View.Scene) (id : Nat) (text : String) : View.Scene :=
  { scene with nodes := scene.nodes.map (fun key node =>
      if key == id then { node with properties := { node.properties with text := text } } else node) }

def applyOutput (output : Out) (scene : View.Scene) : Option View.Scene :=
  match output with
  | .changes value => View.applyPatches value.patches scene
  | .ignored _ => some scene
  | .failed _ => none

/-- Reference message sequencing includes every update's commands in declaration order. -/
def updates (app : App) (messages : List app.Msg) (model : app.Model) :
    app.Model × List (Cmd app.Msg) :=
  messages.foldl (fun (model, commands) message =>
    let result := app.update message model
    (result.1, commands ++ result.2)) (model, [])

def startContract (app : App)
    (start : InitInput → Runtime.State app × Out) : Prop :=
  ∀ input,
    let result := start input
    result.1.model = (Runtime.initial app input).1 ∧
    result.1.active = false ∧ result.1.revision = 0 ∧
    effects result.2 = (Runtime.initial app input).2.map Cmd.effect ∧
    applyOutput result.2 {} = some result.1.rendered.scene ∧
    Runtime.CommandRun ⟨0, ∅, by intro id present; simp at present⟩
      (Runtime.initial app input).2 result.1.requests (commands result.2) ∧
    ∃ output, result.2 = .changes output ∧ output.revision = 0 ∧
      output.patches = View.diffScene {} result.1.rendered.scene ∧
      output.subscriptions = Runtime.Subscriptions.changes [] result.1.installed ∧
      output.snapshot = none

def batchContract {Msg : Type}
    (batch : Runtime.RequestState Msg → List (Cmd Msg) → Runtime.RequestState Msg × List Command) : Prop :=
  ∀ state commands, Runtime.CommandRun state commands (batch state commands).1 (batch state commands).2

def nodeContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  Contracts.nodeStepAgreement (fun _ => True) (·.revision) (·.model) (handlers app)
    app.update Cmd.effect effects step

def answerContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  Contracts.answerStepAgreement (fun _ => True) (·.model) (pending app)
    app.update Cmd.effect effects step

def staleNodeContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  Contracts.staleNodeIgnored (fun event state => (step event state).1) (·.revision)

def missingNodeContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state id input, state.rendered.handlers[id]? = none →
    state.rendered.scene.nodes[id]? = none →
    (step (.node state.revision id input) state).1 = state ∧
    effects (step (.node state.revision id input) state).2 = []

def missingAnswerContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state id reply, state.requests.pending[id]? = none →
    (step (.answer id reply) state).1 = state ∧
    effects (step (.answer id reply) state).2 = []

def subscriptionContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state generation id payload,
    let messages := Runtime.Subscriptions.deliver generation id payload state.installed
      (app.subscriptions state.model)
    let intended := updates app messages state.model
    let result := step (.subscription generation id payload) state
    result.1.model = intended.1 ∧ effects result.2 = intended.2.map Cmd.effect ∧
    (messages = [] → result.1 = state)

def lifecycleContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state flag,
    let source := if flag then Source.resume else Source.pause
    let messages := Runtime.Subscriptions.messages source [] (app.subscriptions state.model)
    let intended := updates app messages state.model
    let result := step (.lifecycle flag) state
    result.1.active = flag ∧ result.1.model = intended.1 ∧
      effects result.2 = intended.2.map Cmd.effect

def saveContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  Contracts.savePreservesModel (·.model) (·.revision) (Runtime.snapshot app) step

def controlledTextContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  Contracts.controlledText (·.model) (fun model => (Ui.compile (app.view model)).scene)
    (·.revision) (fun state id => (state.rendered.scene.nodes[id]?).any (fun node => node.kind == .input))
    edited step applyOutput

def sceneContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state event,
    let observed := match event with
      | .node revision id (.text text) =>
        if revision = state.revision && (state.rendered.scene.nodes[id]?).any (fun node => node.kind == .input)
        then edited state.rendered.scene id text else state.rendered.scene
      | _ => state.rendered.scene
    applyOutput (step event state).2 observed = some (step event state).1.rendered.scene

def revisionContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state event output, (step event state).2 = .changes output →
    output.revision = (step event state).1.revision

def subscriptionChangesContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state event output, (step event state).2 = .changes output →
    output.subscriptions = Runtime.Subscriptions.changes state.installed (step event state).1.installed

def freedContract (app : App)
    (step : Event → Option (Runtime.State app) → Option (Runtime.State app)) : Prop :=
  Contracts.freedIsTerminal step

def freeContract (app : App)
    (free : Option (Runtime.State app) → Option (Runtime.State app)) : Prop :=
  Contracts.freeIdempotent free

def consumed {Msg : Type} (state : Runtime.RequestState Msg) (id : Nat) :
    Runtime.RequestState Msg :=
  ⟨state.next, (Runtime.consume id state.pending).2,
    Runtime.consume_bounded state.next state.pending id state.bounded⟩

/-- Connects batch issuance to each actual event; answer issuance starts with the consumed store. -/
def commandContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state event,
    let result := step event state
    let messagesCommands := fun messages => (updates app messages state.model).2
    let issue := fun before expected =>
      Runtime.CommandRun before expected result.1.requests (commands result.2)
    match event with
    | .node revision id input =>
      issue state.requests (if revision = state.revision then
        ((handlers app state id).bind (fun handler => handler input)).toList.flatMap
          (fun message => (app.update message state.model).2) else [])
    | .answer id reply => match state.requests.pending[id]? with
      | none => issue state.requests []
      | some continuation => issue (consumed state.requests id)
          ((continuation reply).toList.flatMap (fun message => (app.update message state.model).2))
    | .subscription generation id payload =>
      issue state.requests (messagesCommands (Runtime.Subscriptions.deliver generation id payload
        state.installed (app.subscriptions state.model)))
    | .lifecycle flag =>
      issue state.requests (messagesCommands (Runtime.Subscriptions.messages
        (if flag then .resume else .pause) [] (app.subscriptions state.model)))
    | .save => issue state.requests []

def observed (app : App) (state : Runtime.State app) (event : Event) : View.Scene :=
  match event with
  | .node revision id (.text text) =>
    if revision = state.revision && (state.rendered.scene.nodes[id]?).any (fun node => node.kind == .input)
    then edited state.rendered.scene id text else state.rendered.scene
  | _ => state.rendered.scene

/-- Rendering uses one diff from the observed old scene to the final current view. -/
def patchContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state event output, (step event state).2 = .changes output →
    output.patches = View.diffScene (observed app state event) (step event state).1.rendered.scene

/-- Final-scene equality alone would allow echoing an accepted text edit. -/
def noEchoContract (app : App)
    (step : Event → Runtime.State app → Runtime.State app × Out) : Prop :=
  ∀ state id text old new,
    state.rendered.scene.nodes[id]? = some old → old.kind = .input →
    (step (.node state.revision id (.text text)) state).1.rendered.scene.nodes[id]? = some new →
    new.kind = .input → new.properties.text = text →
    ∀ value, Patch.property id (.text value) ∉ patches (step (.node state.revision id (.text text)) state).2

end Kotlean.Runtime.Laws
