import Kotlean.Protocol
import Std.Data.ExtTreeMap.Lemmas

namespace Kotlean.View

structure Node where
  kind : NodeKind
  properties : Properties := {}
  children : List Nat := []
  deriving DecidableEq, Repr

structure Scene where
  nodes : Std.ExtTreeMap Nat Node := ∅
  root : Option Nat := none

end Kotlean.View
