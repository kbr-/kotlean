module
public import Kotlean.Protocol
public import Std.Data.ExtTreeMap.Lemmas

@[expose] public section

namespace Kotlean.View

structure Node where
  kind : NodeKind
  properties : Properties := {}
  children : List Nat := []
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Scene where
  nodes : Std.ExtTreeMap Nat Node := ∅
  root : Option Nat := none

end Kotlean.View
