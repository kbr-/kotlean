import Kotlean.Protocol

namespace Kotlean.Runtime.Contracts

abbrev Handlers (Msg : Type) := Nat → Option (Input → Option Msg)
abbrev Pending (Msg : Type) := Nat → Option (Reply → Msg)

def staleNodeIgnored {State : Type} (step : Event → State → State)
    (revision : State → Nat) : Prop :=
  ∀ state old id payload, old ≠ revision state → step (.node old id payload) state = state

def freedIsTerminal {State : Type} (step : Event → Option State → Option State) : Prop :=
  ∀ event, step event none = none

def freeIdempotent {State : Type} (free : Option State → Option State) : Prop :=
  (∀ state, free state = none) ∧ ∀ state, free (free state) = free state

def savePreservesModel {State Model : Type} (model : State → Model)
    (revision : State → Nat) (save : Model → Option (List UInt8))
    (step : Event → State → State × Out) : Prop :=
  ∀ state, (step .save state).1 = state ∧
    ∃ output, (step .save state).2 = .changes output ∧
      output.revision = revision state ∧ output.snapshot = save (model state) ∧ output.patches = [] ∧
      output.commands = [] ∧ output.subscriptions = []

def controlledText {State Model Render : Type}
    (model : State → Model) (view : Model → Render)
    (revision : State → Nat) (isInput : State → Nat → Bool)
    (edited : Render → Nat → String → Render)
    (step : Event → State → State × Out) (apply : Out → Render → Option Render) : Prop :=
  ∀ state id text, isInput state id = true →
    apply (step (.node (revision state) id (.text text)) state).2
      (edited (view (model state)) id text) = some (view (model (step
        (.node (revision state) id (.text text)) state).1))

def nodeStepAgreement {State Model Msg Cmd : Type} (valid : State → Prop)
    (revision : State → Nat) (model : State → Model) (handlers : State → Handlers Msg)
    (update : Msg → Model → Model × List Cmd) (effect : Cmd → Effect)
    (effects : Out → List Effect) (step : Event → State → State × Out) : Prop :=
  ∀ state id input, valid state →
    let intended := (handlers state id).bind (fun handler => handler input)
    let result := step (.node (revision state) id input) state
    model result.1 = (intended.map (fun msg => (update msg (model state)).1)).getD (model state) ∧
    effects result.2 = (intended.map (fun msg => (update msg (model state)).2.map effect)).getD []

def answerStepAgreement {State Model Msg Cmd : Type} (valid : State → Prop)
    (model : State → Model) (pending : State → Pending (Option Msg))
    (update : Msg → Model → Model × List Cmd) (effect : Cmd → Effect)
    (effects : Out → List Effect) (step : Event → State → State × Out) : Prop :=
  ∀ state id reply, valid state →
    let intended := (pending state id).bind (fun continuation => continuation reply)
    let result := step (.answer id reply) state
    model result.1 = (intended.map (fun msg => (update msg (model state)).1)).getD (model state) ∧
    effects result.2 = (intended.map (fun msg => (update msg (model state)).2.map effect)).getD [] ∧
    pending result.1 id = none

end Kotlean.Runtime.Contracts
