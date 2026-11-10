import Kotlean.Runtime.Commands
import Kotlean.Runtime.Observation

namespace Kotlean.Runtime

def assemble (app : App) (model : app.Model) (revision : Nat) (requests : RequestState app.Msg)
    (active : Bool) (previous : Option (State app)) : State app :=
  let old := (previous.map State.installed).getD []
  let next := (previous.map State.nextSubscription).getD 0
  have invariants : (old.map Subscription.source).Nodup ∧ (old.map Subscription.id).Nodup ∧
      ∀ binding ∈ old, binding.id < next := by
    cases previous with
    | none => simp [old]
    | some previous => exact ⟨previous.sourceUnique, previous.idUnique, previous.subscriptionBound⟩
  let sources := Subscriptions.desired active (app.subscriptions model)
  let result := Subscriptions.reconcile next old sources
  have valid := Subscriptions.reconcile_valid next old sources
    invariants.1 invariants.2.1 invariants.2.2
  { model := model
    rendered := Ui.compile (app.view model)
    rendered_current := rfl
    revision := revision
    requests := requests
    active := active
    installed := result.1
    nextSubscription := result.2
    sourceUnique := valid.1
    idUnique := valid.2.1
    subscriptionBound := valid.2.2
    sourcesCurrent := by
      intro source
      constructor
      · intro member
        obtain ⟨binding, member, same⟩ := List.mem_map.mp member
        rw [← same]
        exact Subscriptions.reconcile_sources next old sources binding member
      · intro wanted
        obtain ⟨binding, member, same⟩ := Subscriptions.reconcile_covers next old sources source wanted
        exact List.mem_map.mpr ⟨binding, member, same⟩ }

def changes (oldScene : View.Scene) (oldBindings : List Subscription) (state : State app)
    (commands : List Command) : Out :=
  .changes {
    revision := state.revision
    patches := View.diffScene oldScene state.rendered.scene
    commands := commands
    subscriptions := Subscriptions.changes oldBindings state.installed
    snapshot := none
  }

def updates (app : App) (messages : List app.Msg) (model : app.Model) :
    app.Model × List (Cmd app.Msg) :=
  messages.foldl (fun (model, commands) message =>
    let result := app.update message model
    (result.1, commands ++ result.2)) (model, [])

def transition (state : State app) (messages : List app.Msg) (requests : RequestState app.Msg)
    (active : Bool) (oldScene : View.Scene) : State app × Out :=
  let updated := updates app messages state.model
  let issued := RequestState.batch requests updated.2
  let next := assemble app updated.1 (state.revision + 1) issued.1 active (some state)
  (next, changes oldScene state.installed next issued.2)

def start (app : App) (input : InitInput) : State app × Out :=
  let selected := initial app input
  let issued := RequestState.batch RequestState.empty selected.2
  let state := assemble app selected.1 0 issued.1 false none
  (state, changes {} [] state issued.2)

def dispatch (state : State app) (id : Nat) (input : Input) : Option app.Msg :=
  (state.rendered.handlers[id]?).bind (fun handler => handler.dispatch input)

def step (event : Event) (state : State app) : State app × Out :=
  match event with
  | .node revision id input =>
    if revision != state.revision then (state, .ignored none)
    else
      let message := dispatch state id input
      match message, isTextEdit state.rendered.scene id input with
      | none, false => (state, .ignored none)
      | _, _ => transition state message.toList state.requests state.active
          (observed state.rendered.scene state.revision event)
  | .answer id reply =>
    let taken := state.requests.take id
    match taken.1 with
    | none => (state, .ignored none)
    | some continuation =>
      match continuation reply with
      | none => ({ state with requests := taken.2 }, .ignored none)
      | some message => transition state [message] taken.2 state.active state.rendered.scene
  | .subscription generation id payload =>
    let messages := Subscriptions.deliver generation id payload state.installed
      (app.subscriptions state.model)
    match messages with
    | [] => (state, .ignored none)
    | _ :: _ => transition state messages state.requests state.active state.rendered.scene
  | .lifecycle active =>
    let messages := Subscriptions.messages (if active then .resume else .pause) []
      (app.subscriptions state.model)
    transition state messages state.requests active state.rendered.scene
  | .save =>
    (state, .changes {
      revision := state.revision
      patches := []
      commands := []
      subscriptions := []
      snapshot := snapshot app state.model
    })

def stepOptional (event : Event) (state : Option (State app)) : Option (State app) × Out :=
  match state with
  | none => (none, .ignored none)
  | some state =>
    let result := step event state
    (some result.1, result.2)

def free (_ : Option (State app)) : Option (State app) := none

end Kotlean.Runtime
