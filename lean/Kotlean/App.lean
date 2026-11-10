module
public import Kotlean.Ui.Types
public import Std.Data.ExtTreeMap

@[expose] public section

namespace Kotlean

structure Cmd (Msg : Type) where
  effect : Effect
  answer : Option (Reply → Option Msg) := none

structure Sub (Msg : Type) where
  source : Source
  receive : List UInt8 → Option Msg

structure Persistence (Model : Type) where
  save : Model → List UInt8
  restore : List UInt8 → Option Model

structure App where
  Model : Type
  Msg : Type
  init : Model × List (Cmd Msg)
  update : Msg → Model → Model × List (Cmd Msg)
  view : Model → Ui Msg
  subscriptions : Model → List (Sub Msg) := fun _ => []
  persistence : Option (Persistence Model) := none

namespace Runtime

abbrev Pending (Msg : Type) := Std.ExtTreeMap Nat (Reply → Option Msg) compare

end Runtime
end Kotlean
