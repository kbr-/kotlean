import Kotlean.Runtime.Requests
import Kotlean.Runtime.SubscriptionProofs
import Kotlean.Ui.Canonical

namespace Kotlean.Runtime

structure RequestState (Msg : Type) where
  next : Nat
  pending : Pending Msg
  bounded : ∀ id, (pending[id]?).isSome → id < next

inductive CommandRun {Msg : Type} : RequestState Msg → List (Cmd Msg) →
    RequestState Msg → List Command → Prop where
  | nil (state) : CommandRun state [] state []
  | cons {state advanced final command output commands outputs}
      (issued : issue state.next state.pending command = (output, advanced.next, advanced.pending))
      (rest : CommandRun advanced commands final outputs) :
      CommandRun state (command :: commands) final (output :: outputs)

structure State (app : App) where
  model : app.Model
  rendered : Ui.Rendered app.Msg
  rendered_current : rendered = Ui.compile (app.view model)
  revision : Nat
  requests : RequestState app.Msg
  active : Bool
  installed : List Subscription
  nextSubscription : Nat
  sourceUnique : (installed.map Subscription.source).Nodup
  idUnique : (installed.map Subscription.id).Nodup
  subscriptionBound : ∀ binding ∈ installed, binding.id < nextSubscription
  sourcesCurrent : ∀ source, source ∈ installed.map Subscription.source ↔
    source ∈ Subscriptions.desired active (app.subscriptions model)

end Kotlean.Runtime
