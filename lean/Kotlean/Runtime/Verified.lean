import Kotlean.Runtime.Laws
import Kotlean.Runtime.Engine
import Kotlean.Runtime.ObservationProofs

namespace Kotlean.Runtime.Verified

namespace KotleanStepSpec
export Kotlean.Runtime.Laws (effects commands patches handlers pending edited applyOutput updates
  startContract batchContract nodeContract answerContract staleNodeContract missingNodeContract
  missingAnswerContract subscriptionContract lifecycleContract saveContract controlledTextContract
  sceneContract revisionContract subscriptionChangesContract freedContract freeContract consumed
  commandContract observed patchContract noEchoContract)
end KotleanStepSpec
open Kotlean

theorem batch {Msg : Type} :
    KotleanStepSpec.batchContract (Runtime.RequestState.batch (Msg := Msg)) :=
  Runtime.RequestState.batch_run

theorem stale_node (app : App) : KotleanStepSpec.staleNodeContract app Runtime.step := by
  intro state revision id input different
  simp [Runtime.step, different]

theorem missing_answer (app : App) : KotleanStepSpec.missingAnswerContract app Runtime.step := by
  intro state id reply absent
  simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, absent, KotleanStepSpec.effects]

private theorem transition_effects (state : Runtime.State app) (messages : List app.Msg)
    (requests : Runtime.RequestState app.Msg) (active : Bool) (scene : View.Scene) :
    KotleanStepSpec.effects (Runtime.transition state messages requests active scene).2 =
      (KotleanStepSpec.updates app messages state.model).2.map Cmd.effect := by
  change (Runtime.RequestState.batch requests (Runtime.updates app messages state.model).2).2.map Command.effect = _
  exact Runtime.CommandRun.effects (Runtime.RequestState.batch_run _ _)

private theorem transition_one (state : Runtime.State app) (message : app.Msg)
    (requests : Runtime.RequestState app.Msg) (active : Bool) (scene : View.Scene) :
    (Runtime.transition state [message] requests active scene).1.model =
      (app.update message state.model).1 ∧
    KotleanStepSpec.effects (Runtime.transition state [message] requests active scene).2 =
      (app.update message state.model).2.map Cmd.effect :=
  ⟨rfl, transition_effects _ _ _ _ _⟩

private theorem transition_empty (state : Runtime.State app)
    (requests : Runtime.RequestState app.Msg) (active : Bool) (scene : View.Scene) :
    (Runtime.transition state [] requests active scene).1.model = state.model ∧
    KotleanStepSpec.effects (Runtime.transition state [] requests active scene).2 = [] :=
  ⟨rfl, transition_effects _ _ _ _ _⟩

private theorem handlers_dispatch (state : Runtime.State app) (id : Nat) (input : Input) :
    ((KotleanStepSpec.handlers app state id).bind (fun handler => handler input)) =
      Runtime.dispatch state id input := by
  cases found : state.rendered.handlers[id]? <;>
    simp [KotleanStepSpec.handlers, Runtime.dispatch, found]

theorem node (app : App) : KotleanStepSpec.nodeContract app Runtime.step := by
  intro state id input _
  rw [handlers_dispatch]
  cases selected : Runtime.dispatch state id input with
  | none =>
    cases edit : Runtime.isTextEdit state.rendered.scene id input with
    | false => simp [Runtime.step, selected, edit, KotleanStepSpec.effects]
    | true =>
      simpa [Runtime.step, selected, edit] using transition_empty state state.requests state.active
        (Runtime.observed state.rendered.scene state.revision (.node state.revision id input))

  | some message =>
    cases edit : Runtime.isTextEdit state.rendered.scene id input <;>
      simpa [Runtime.step, selected, edit] using transition_one state message state.requests state.active
        (Runtime.observed state.rendered.scene state.revision (.node state.revision id input))

theorem missing_node (app : App) : KotleanStepSpec.missingNodeContract app Runtime.step := by
  intro state id input handlerAbsent nodeAbsent
  have absent : Runtime.dispatch state id input = none := by
    simp [Runtime.dispatch, handlerAbsent]
  cases input <;> simp [Runtime.step, absent, Runtime.isTextEdit, nodeAbsent, KotleanStepSpec.effects]

private theorem transition_run (state : Runtime.State app) (messages : List app.Msg)
    (requests : Runtime.RequestState app.Msg) (active : Bool) (scene : View.Scene) :
    Runtime.CommandRun requests (KotleanStepSpec.updates app messages state.model).2
      (Runtime.transition state messages requests active scene).1.requests
      (KotleanStepSpec.commands (Runtime.transition state messages requests active scene).2) :=
  Runtime.RequestState.batch_run _ _

theorem answer (app : App) : KotleanStepSpec.answerContract app Runtime.step := by
  intro state id reply _
  cases selected : state.requests.pending[id]? with
  | none =>
    simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected,
      KotleanStepSpec.pending, KotleanStepSpec.effects]
  | some continuation =>
    cases message : continuation reply with
    | none =>
      simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message,
        KotleanStepSpec.pending, KotleanStepSpec.effects]
    | some value =>
      have bound : id < state.requests.next := state.requests.bounded id (by simp [selected])
      have retained := Runtime.CommandRun.older
        (transition_run state [value] (state.requests.take id).2 state.active state.rendered.scene)
        id bound
      have absent : (Runtime.transition state [value] (state.requests.take id).2 state.active
          state.rendered.scene).1.requests.pending[id]? = none :=
        retained.trans (Runtime.consume_selected id state.requests.pending).2.1
      have one := transition_one state value (state.requests.take id).2 state.active state.rendered.scene
      simpa [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message,
        KotleanStepSpec.pending] using And.intro one.1 (And.intro one.2 absent)

theorem start (app : App) : KotleanStepSpec.startContract app (Runtime.start app) := by
  intro input
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact Runtime.CommandRun.effects (Runtime.RequestState.batch_run _ _)
  · apply View.diffScene_correct
    · simp [View.Canonical.valid, View.Canonical.preorder]
    · exact Ui.compile_canonical _
  · exact Runtime.RequestState.batch_run _ _
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem commands (app : App) : KotleanStepSpec.commandContract app Runtime.step := by
  intro state event
  cases event with
  | node revision id input =>
    dsimp only
    rw [handlers_dispatch]
    by_cases current : revision = state.revision
    · subst revision
      cases selected : Runtime.dispatch state id input with
      | none =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input with
        | false => simpa [Runtime.step, selected, edit, KotleanStepSpec.commands] using Runtime.CommandRun.nil state.requests
        | true =>
          simpa [Runtime.step, selected, edit, KotleanStepSpec.updates] using transition_run state [] state.requests state.active
            (Runtime.observed state.rendered.scene state.revision (.node state.revision id input))
      | some message =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input <;>
          simpa [Runtime.step, selected, edit, KotleanStepSpec.updates] using transition_run state [message] state.requests state.active
            (Runtime.observed state.rendered.scene state.revision (.node state.revision id input))
    · simpa [Runtime.step, current, KotleanStepSpec.commands] using Runtime.CommandRun.nil state.requests
  | answer id reply =>
    cases selected : state.requests.pending[id]? with
    | none =>
      simpa [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, KotleanStepSpec.commands]
        using Runtime.CommandRun.nil state.requests
    | some continuation =>
      cases message : continuation reply with
      | none =>
        simpa [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message,
          KotleanStepSpec.consumed, KotleanStepSpec.commands] using
            Runtime.CommandRun.nil (KotleanStepSpec.consumed state.requests id)
      | some value =>
        simpa [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message,
          KotleanStepSpec.consumed, KotleanStepSpec.updates] using transition_run state [value]
            (KotleanStepSpec.consumed state.requests id) state.active state.rendered.scene
  | subscription generation id payload =>
    cases delivered : Runtime.Subscriptions.deliver generation id payload state.installed
        (app.subscriptions state.model) with
    | nil => simpa [Runtime.step, delivered, KotleanStepSpec.updates, KotleanStepSpec.commands] using
        Runtime.CommandRun.nil state.requests
    | cons message messages =>
      simpa [Runtime.step, delivered] using transition_run state (message :: messages)
        state.requests state.active state.rendered.scene
  | lifecycle active => exact transition_run _ _ _ _ _
  | save => exact Runtime.CommandRun.nil state.requests

theorem lifecycle (app : App) : KotleanStepSpec.lifecycleContract app Runtime.step := by
  intro state active
  exact ⟨rfl, rfl, transition_effects _ _ _ _ _⟩

theorem save (app : App) : KotleanStepSpec.saveContract app Runtime.step := by
  intro state
  exact ⟨rfl, ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem subscription (app : App) : KotleanStepSpec.subscriptionContract app Runtime.step := by
  intro state generation id payload
  cases delivered : Runtime.Subscriptions.deliver generation id payload state.installed
      (app.subscriptions state.model) with
  | nil => simp [Runtime.step, delivered, KotleanStepSpec.updates, KotleanStepSpec.effects]
  | cons message messages =>
    simp only [Runtime.step, delivered]
    exact ⟨rfl, transition_effects _ _ _ _ _, by simp⟩

theorem freed (app : App) : KotleanStepSpec.freedContract app
    (fun event state => (Runtime.stepOptional event state).1) := by
  intro event
  rfl

theorem free (app : App) : KotleanStepSpec.freeContract app Runtime.free :=
  ⟨fun _ => rfl, fun _ => rfl⟩

private theorem observed_agrees (state : Runtime.State app) (event : Event) :
    Runtime.observed state.rendered.scene state.revision event = KotleanStepSpec.observed app state event := by
  cases event with
  | node revision id input => cases input <;>
      simp [Runtime.observed, KotleanStepSpec.observed, Runtime.edited, KotleanStepSpec.edited]
  | answer | subscription | lifecycle | save => rfl

private theorem transition_fields (state : Runtime.State app) (messages : List app.Msg)
    (requests : Runtime.RequestState app.Msg) (active : Bool) (scene : View.Scene) (output : Output)
    (equal : (Runtime.transition state messages requests active scene).2 = .changes output) :
    output.revision = (Runtime.transition state messages requests active scene).1.revision ∧
    output.subscriptions = Runtime.Subscriptions.changes state.installed
      (Runtime.transition state messages requests active scene).1.installed ∧
    output.patches = View.diffScene scene (Runtime.transition state messages requests active scene).1.rendered.scene := by
  cases equal
  exact ⟨rfl, rfl, rfl⟩

private theorem event_transition_fields (state : Runtime.State app) (event : Event)
    (messages : List app.Msg) (requests : Runtime.RequestState app.Msg) (active : Bool)
    (transition : Runtime.step event state = Runtime.transition state messages requests active
      (Runtime.observed state.rendered.scene state.revision event)) (output : Output)
    (equal : (Runtime.step event state).2 = .changes output) :
    output.revision = (Runtime.step event state).1.revision ∧
    output.subscriptions = Runtime.Subscriptions.changes state.installed (Runtime.step event state).1.installed ∧
    output.patches = View.diffScene (Runtime.observed state.rendered.scene state.revision event)
      (Runtime.step event state).1.rendered.scene := by
  rw [transition] at equal ⊢
  exact transition_fields _ _ _ _ _ _ equal

private theorem step_fields (state : Runtime.State app) (event : Event) (output : Output)
    (equal : (Runtime.step event state).2 = .changes output) :
    output.revision = (Runtime.step event state).1.revision ∧
    output.subscriptions = Runtime.Subscriptions.changes state.installed (Runtime.step event state).1.installed ∧
    output.patches = View.diffScene (Runtime.observed state.rendered.scene state.revision event)
      (Runtime.step event state).1.rendered.scene := by
  cases event with
  | node revision id input =>
    by_cases current : revision = state.revision
    · subst revision
      cases selected : Runtime.dispatch state id input with
      | none =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input with
        | false => simp [Runtime.step, selected, edit] at equal
        | true =>
          exact event_transition_fields state _ [] state.requests state.active
            (by simp [Runtime.step, selected, edit]) output equal
      | some message =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input <;>
          exact event_transition_fields state _ [message] state.requests state.active
            (by simp [Runtime.step, selected, edit]) output equal
    · simp [Runtime.step, current] at equal
  | answer id reply =>
    cases selected : state.requests.pending[id]? with
    | none => simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected] at equal
    | some continuation =>
      cases message : continuation reply with
      | none => simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message] at equal
      | some value =>
        exact event_transition_fields state _ [value] (state.requests.take id).2 state.active
          (by simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message, Runtime.observed]) output equal
  | subscription generation id payload =>
    cases delivered : Runtime.Subscriptions.deliver generation id payload state.installed
        (app.subscriptions state.model) with
    | nil => simp [Runtime.step, delivered] at equal
    | cons message messages =>
      exact event_transition_fields state _ (message :: messages) state.requests state.active
        (by simp [Runtime.step, delivered, Runtime.observed]) output equal
  | lifecycle active => exact event_transition_fields state _ _ _ _ rfl output equal
  | save =>
    simp only [Runtime.step, Out.changes.injEq] at equal
    cases equal
    exact ⟨rfl, (Runtime.Subscriptions.changes_unchanged _).symm, (View.diffScene_self _).symm⟩

theorem revision (app : App) : KotleanStepSpec.revisionContract app Runtime.step := by
  intro state event output equal
  exact (step_fields state event output equal).1

theorem subscription_changes (app : App) : KotleanStepSpec.subscriptionChangesContract app Runtime.step := by
  intro state event output equal
  exact (step_fields state event output equal).2.1

theorem patches (app : App) : KotleanStepSpec.patchContract app Runtime.step := by
  intro state event output equal
  simpa only [observed_agrees] using (step_fields state event output equal).2.2

private theorem rendered_valid (state : Runtime.State app) : View.Canonical.valid state.rendered.scene := by
  rw [state.rendered_current]
  exact Ui.compile_canonical _

private theorem nonchanges (state : Runtime.State app) (event : Event) :
    match (Runtime.step event state).2 with
    | .changes _ => True
    | .ignored _ => (Runtime.step event state).1.rendered.scene =
        Runtime.observed state.rendered.scene state.revision event
    | .failed _ => False := by
  cases event with
  | node revision id input =>
    by_cases current : revision = state.revision
    · subst revision
      cases selected : Runtime.dispatch state id input with
      | none =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input with
        | false =>
          cases input <;> simp_all [Runtime.step, Runtime.isTextEdit, Runtime.observed]
        | true => simp [Runtime.step, selected, edit, Runtime.transition, Runtime.changes]
      | some message =>
        cases edit : Runtime.isTextEdit state.rendered.scene id input <;>
          simp [Runtime.step, selected, edit, Runtime.transition, Runtime.changes]
    · cases input <;> simp [Runtime.step, current, Runtime.observed]
  | answer id reply =>
    cases selected : state.requests.pending[id]? with
    | none => simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, Runtime.observed]
    | some continuation =>
      cases message : continuation reply <;>
        simp [Runtime.step, Runtime.RequestState.take, Runtime.consume, selected, message,
          Runtime.observed, Runtime.transition, Runtime.changes]
  | subscription generation id payload =>
    cases delivered : Runtime.Subscriptions.deliver generation id payload state.installed
        (app.subscriptions state.model) <;>
      simp [Runtime.step, delivered, Runtime.observed, Runtime.transition, Runtime.changes]
  | lifecycle active => trivial
  | save => trivial

theorem scene (app : App) : KotleanStepSpec.sceneContract app Runtime.step := by
  intro state event
  change KotleanStepSpec.applyOutput (Runtime.step event state).2 (KotleanStepSpec.observed app state event) = _
  rw [← observed_agrees]
  cases output : (Runtime.step event state).2 with
  | changes value =>
    change View.applyPatches value.patches _ = _
    rw [(step_fields state event value output).2.2]
    exact View.diffScene_correct _ _
      (Runtime.observed_valid _ _ _ (rendered_valid state)) (rendered_valid _)
  | ignored diagnostic =>
    have same := nonchanges state event
    rw [output] at same
    exact congrArg some same.symm
  | failed message =>
    have impossible := nonchanges state event
    simp [output] at impossible

theorem text (app : App) : KotleanStepSpec.controlledTextContract app Runtime.step := by
  intro state id value isInput
  have result := scene app state (.node state.revision id (.text value))
  change KotleanStepSpec.applyOutput _
    (KotleanStepSpec.observed app state (.node state.revision id (.text value))) = _ at result
  simp [KotleanStepSpec.observed, isInput] at result
  simpa only [state.rendered_current, (Runtime.step (.node state.revision id (.text value)) state).1.rendered_current]
    using result

theorem no_echo (app : App) : KotleanStepSpec.noEchoContract app Runtime.step := by
  intro state id value old new oldLookup oldKind newLookup newKind newText text
  let event := Event.node state.revision id (.text value)
  cases output : (Runtime.step event state).2 with
  | changes result =>
    change Patch.property id (.text text) ∉ result.patches
    rw [patches app state event result output]
    have observedLookup : (KotleanStepSpec.observed app state event).nodes[id]? =
        some { old with properties := { old.properties with text := value } } := by
      simp [KotleanStepSpec.observed, KotleanStepSpec.edited, event, oldLookup, oldKind]
    exact View.diffScene_text_unchanged _ _ id _ new observedLookup newLookup
      (by simp [oldKind, newKind]) (by simp [newText]) text
  | ignored diagnostic => simp [KotleanStepSpec.patches]
  | failed message => simp [KotleanStepSpec.patches]

end Kotlean.Runtime.Verified
