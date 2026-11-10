module
public import Kotlean.Ui.Types

@[expose] public section

namespace Kotlean.Ui.Laws

def maskContract {Msg : Type} (mask : Handlers Msg → ListenerMask) : Prop :=
  ∀ handlers, mask handlers =
    { click := handlers.click.isSome, text := handlers.text.isSome,
      touch := handlers.touch.isSome, key := handlers.key.isSome, resize := handlers.resize.isSome }

def dispatchContract {Msg : Type} (dispatch : Handlers Msg → Input → Option Msg) : Prop :=
  (∀ handlers, dispatch handlers .click = handlers.click) ∧
  (∀ handlers text, dispatch handlers (.text text) = handlers.text.map (fun f => f text)) ∧
  (∀ handlers frame, dispatch handlers (.touch frame) = handlers.touch.map (fun f => f frame)) ∧
  (∀ handlers code down, dispatch handlers (.key code down) = handlers.key.map (fun f => f code down)) ∧
  (∀ handlers width height density, dispatch handlers (.resize width height density) =
    handlers.resize.map (fun f => f width height density))

def propertiesContract {Msg : Type} (mask : Handlers Msg → ListenerMask)
    (properties : Attributes Msg → Properties) : Prop :=
  ∀ attributes, properties attributes =
    { attributes.toProperties with listeners := mask attributes.events }

inductive NodeForm {Msg : Type} : Ui Msg → NodeKind → Attributes Msg → List (Ui Msg) → Prop where
  | column (attributes : Attributes Msg) (children : List (Ui Msg)) :
      NodeForm (.column attributes children) .column attributes children
  | row (attributes : Attributes Msg) (children : List (Ui Msg)) :
      NodeForm (.row attributes children) .row attributes children
  | text (attributes : Attributes Msg) : NodeForm (.text attributes) .text attributes []
  | button (attributes : Attributes Msg) : NodeForm (.button attributes) .button attributes []
  | input (attributes : Attributes Msg) : NodeForm (.input attributes) .input attributes []
  | scroll (attributes : Attributes Msg) (child : Ui Msg) :
      NodeForm (.scroll attributes child) .scroll attributes [child]
  | canvas (attributes : Attributes Msg) : NodeForm (.canvas attributes) .canvas attributes []

mutual
  inductive Layout {Msg : Type} (properties : Attributes Msg → Properties) : Ui Msg → Nat → Chunk Msg → Prop where
    | empty (start : Nat) : Layout properties .empty start { next := start }
    | node (tree : Ui Msg) (kind : NodeKind) (attributes : Attributes Msg) (children : List (Ui Msg))
        (form : NodeForm tree kind attributes children) (start : Nat) (forest : Forest Msg)
        (rendered : ForestLayout properties children (start + 1) forest) :
        Layout properties tree start
          { next := forest.next, root := some start,
            nodes := (start, { kind := kind, properties := properties attributes, children := forest.roots }) :: forest.nodes,
            handlers := (start, attributes.events) :: forest.handlers }

  inductive ForestLayout {Msg : Type} (properties : Attributes Msg → Properties) :
      List (Ui Msg) → Nat → Forest Msg → Prop where
    | nil (start : Nat) : ForestLayout properties [] start { next := start }
    | cons (tree : Ui Msg) (rest : List (Ui Msg)) (start : Nat) (first : Chunk Msg) (following : Forest Msg)
        (rendered : Layout properties tree start first)
        (continued : ForestLayout properties rest first.next following) :
        ForestLayout properties (tree :: rest) start
          { next := following.next, roots := first.root.toList ++ following.roots,
            nodes := first.nodes ++ following.nodes, handlers := first.handlers ++ following.handlers }
end

def layoutContract {Msg : Type} (properties : Attributes Msg → Properties)
    (compile : Ui Msg → Rendered Msg) : Prop :=
  ∀ tree, ∃ chunk, Layout properties tree 0 chunk ∧
    (compile tree).scene = { nodes := Std.ExtTreeMap.ofList chunk.nodes, root := chunk.root } ∧
    (compile tree).handlers = Std.ExtTreeMap.ofList chunk.handlers

def canonicalContract {Msg : Type} (compile : Ui Msg → Rendered Msg) : Prop :=
  ∀ tree, View.Canonical.valid (compile tree).scene

def bindingsContract {Msg : Type} (compile : Ui Msg → Rendered Msg) : Prop :=
  ∀ (tree : Ui Msg) (id : Nat), (compile tree).scene.nodes[id]?.isSome = (compile tree).handlers[id]?.isSome

mutual
 inductive SameShape {Left Right : Type} (leftProperties : Attributes Left → Properties)
    (rightProperties : Attributes Right → Properties) : Ui Left → Ui Right → Prop where
  | empty : SameShape leftProperties rightProperties .empty .empty
  | node (leftTree : Ui Left) (rightTree : Ui Right) (kind : NodeKind)
      (left : Attributes Left) (right : Attributes Right)
      (leftChildren : List (Ui Left)) (rightChildren : List (Ui Right))
      (leftForm : NodeForm leftTree kind left leftChildren)
      (rightForm : NodeForm rightTree kind right rightChildren)
      (attributes : leftProperties left = rightProperties right)
      (children : SameForest leftProperties rightProperties leftChildren rightChildren) :
      SameShape leftProperties rightProperties
        leftTree rightTree

 inductive SameForest {Left Right : Type} (leftProperties : Attributes Left → Properties)
     (rightProperties : Attributes Right → Properties) : List (Ui Left) → List (Ui Right) → Prop where
   | nil : SameForest leftProperties rightProperties [] []
   | cons (left : Ui Left) (right : Ui Right) (leftRest : List (Ui Left)) (rightRest : List (Ui Right))
       (head : SameShape leftProperties rightProperties left right)
       (tail : SameForest leftProperties rightProperties leftRest rightRest) :
       SameForest leftProperties rightProperties (left :: leftRest) (right :: rightRest)
end

def shapeContract {Left Right : Type} (leftProperties : Attributes Left → Properties)
    (rightProperties : Attributes Right → Properties)
    (leftCompile : Ui Left → Rendered Left) (rightCompile : Ui Right → Rendered Right) : Prop :=
  ∀ left right, SameShape leftProperties rightProperties left right →
    (leftCompile left).scene = (rightCompile right).scene

end Kotlean.Ui.Laws
