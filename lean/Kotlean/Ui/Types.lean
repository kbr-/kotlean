module
public import Kotlean.View.Canonical

@[expose] public section

namespace Kotlean

structure Handlers (Msg : Type) where
  click : Option Msg := none
  text : Option (String → Msg) := none
  touch : Option (TouchFrame → Msg) := none
  key : Option (Nat → Bool → Msg) := none
  resize : Option (Nat → Nat → Nat → Msg) := none

structure Attributes (Msg : Type) extends Properties where
  events : Handlers Msg := {}

inductive Ui (Msg : Type) where
  | empty
  | column (attributes : Attributes Msg) (children : List (Ui Msg))
  | row (attributes : Attributes Msg) (children : List (Ui Msg))
  | text (attributes : Attributes Msg)
  | button (attributes : Attributes Msg)
  | input (attributes : Attributes Msg)
  | scroll (attributes : Attributes Msg) (child : Ui Msg)
  | canvas (attributes : Attributes Msg)

namespace Ui

structure Chunk (Msg : Type) where
  next : Nat
  root : Option Nat := none
  nodes : List (Nat × View.Node) := []
  handlers : List (Nat × Handlers Msg) := []

structure Forest (Msg : Type) where
  next : Nat
  roots : List Nat := []
  nodes : List (Nat × View.Node) := []
  handlers : List (Nat × Handlers Msg) := []

structure Rendered (Msg : Type) where
  scene : View.Scene
  handlers : Std.ExtTreeMap Nat (Handlers Msg)

end Ui
end Kotlean
