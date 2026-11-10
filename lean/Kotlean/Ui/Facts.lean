module
public import Kotlean.Ui.Compile
public import Kotlean.View.Application

@[expose] public section

namespace Kotlean.Ui

theorem layout_mutual {Msg : Type} (properties : Attributes Msg → Properties)
    (P : Ui Msg → Nat → Chunk Msg → Prop) (Q : List (Ui Msg) → Nat → Forest Msg → Prop)
    (empty : ∀ start, P .empty start { next := start })
    (node : ∀ tree kind attributes children (_form : Laws.NodeForm tree kind attributes children)
      start forest (_rendered : Laws.ForestLayout properties children (start + 1) forest),
      Q children (start + 1) forest →
      P tree start
        { next := forest.next, root := some start,
          nodes := (start, { kind := kind, properties := properties attributes, children := forest.roots }) :: forest.nodes,
          handlers := (start, attributes.events) :: forest.handlers })
    (nil : ∀ start, Q [] start { next := start })
    (cons : ∀ tree rest start first following (_rendered : Laws.Layout properties tree start first)
      (_continued : Laws.ForestLayout properties rest first.next following),
      P tree start first → Q rest first.next following →
      Q (tree :: rest) start
        { next := following.next, roots := first.root.toList ++ following.roots,
          nodes := first.nodes ++ following.nodes, handlers := first.handlers ++ following.handlers }) :
    (∀ tree start chunk, Laws.Layout properties tree start chunk → P tree start chunk) ∧
    (∀ trees start forest, Laws.ForestLayout properties trees start forest → Q trees start forest) := by
  constructor
  · intro tree start chunk layout
    exact Laws.Layout.rec (motive_1 := fun t s c _ => P t s c)
      (motive_2 := fun ts s f _ => Q ts s f) empty node nil cons layout
  · intro trees start forest layout
    exact Laws.ForestLayout.rec (motive_1 := fun t s c _ => P t s c)
      (motive_2 := fun ts s f _ => Q ts s f) empty node nil cons layout

private theorem handler_keys_all {Msg : Type} (properties : Attributes Msg → Properties) :
    (∀ tree start chunk, Laws.Layout properties tree start chunk →
      chunk.handlers.map Prod.fst = chunk.nodes.map Prod.fst) ∧
    (∀ trees start forest, Laws.ForestLayout properties trees start forest →
      forest.handlers.map Prod.fst = forest.nodes.map Prod.fst) := by
  apply layout_mutual properties
    (fun _ _ chunk => chunk.handlers.map Prod.fst = chunk.nodes.map Prod.fst)
    (fun _ _ forest => forest.handlers.map Prod.fst = forest.nodes.map Prod.fst)
  · intro start; rfl
  · intro tree kind attributes children form start forest rendered keys
    simpa only [List.map_cons] using congrArg (List.cons start) keys
  · intro start; rfl
  · intro tree rest start first following rendered continued firstKeys followingKeys
    simp only [List.map_append]
    rw [firstKeys, followingKeys]

theorem layout_handler_keys {Msg : Type} (properties : Attributes Msg → Properties)
    (tree : Ui Msg) (start : Nat) (chunk : Chunk Msg) (layout : Laws.Layout properties tree start chunk) :
    chunk.handlers.map Prod.fst = chunk.nodes.map Prod.fst :=
  (handler_keys_all properties).1 tree start chunk layout

theorem forest_handler_keys {Msg : Type} (properties : Attributes Msg → Properties)
    (trees : List (Ui Msg)) (start : Nat) (forest : Forest Msg)
    (layout : Laws.ForestLayout properties trees start forest) :
    forest.handlers.map Prod.fst = forest.nodes.map Prod.fst :=
  (handler_keys_all properties).2 trees start forest layout

theorem compile_bindings {Msg : Type} : Laws.bindingsContract (@compile Msg) := by
  intro tree id
  have keys := layout_handler_keys (@Attributes.renderProperties Msg) tree 0 _ (renderAt_layout tree 0)
  simp only [compile, Std.ExtTreeMap.isSome_getElem?_eq_contains, Std.ExtTreeMap.contains_ofList]
  rw [keys]

theorem render_form {Msg : Type} (tree : Ui Msg) (kind : NodeKind) (attributes : Attributes Msg)
    (children : List (Ui Msg)) (form : Laws.NodeForm tree kind attributes children) (start : Nat) :
    renderAt tree start = nodeChunk start kind attributes (renderForest children (start + 1)) := by
  cases form <;> simp only [renderAt, renderForest, singleForest, List.append_nil]

private theorem render_shape_all {Left Right : Type} :
    (∀ left right, Laws.SameShape (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right →
      ∀ start, (renderAt left start).next = (renderAt right start).next ∧
        (renderAt left start).root = (renderAt right start).root ∧
        (renderAt left start).nodes = (renderAt right start).nodes) ∧
    (∀ left right, Laws.SameForest (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right →
      ∀ start, (renderForest left start).next = (renderForest right start).next ∧
        (renderForest left start).roots = (renderForest right start).roots ∧
        (renderForest left start).nodes = (renderForest right start).nodes) := by
  let P := fun (left : Ui Left) (right : Ui Right) => ∀ start,
    (renderAt left start).next = (renderAt right start).next ∧
    (renderAt left start).root = (renderAt right start).root ∧
    (renderAt left start).nodes = (renderAt right start).nodes
  let Q := fun (left : List (Ui Left)) (right : List (Ui Right)) => ∀ start,
    (renderForest left start).next = (renderForest right start).next ∧
    (renderForest left start).roots = (renderForest right start).roots ∧
    (renderForest left start).nodes = (renderForest right start).nodes
  have empty : P .empty .empty := by intro start; simp [renderAt]
  have node : ∀ leftTree rightTree kind left right leftChildren rightChildren
      (leftForm : Laws.NodeForm leftTree kind left leftChildren)
      (rightForm : Laws.NodeForm rightTree kind right rightChildren)
      (attributes : left.renderProperties = right.renderProperties)
      (children : Laws.SameForest (@Attributes.renderProperties Left) (@Attributes.renderProperties Right)
        leftChildren rightChildren), Q leftChildren rightChildren → P leftTree rightTree := by
    intro leftTree rightTree kind left right leftChildren rightChildren leftForm rightForm attributes children related start
    have fields := related (start + 1)
    rw [render_form leftTree kind left leftChildren leftForm start,
      render_form rightTree kind right rightChildren rightForm start]
    refine ⟨fields.1, rfl, ?_⟩
    simp only [nodeChunk]
    rw [fields.2.1, fields.2.2, attributes]
  have nil : Q [] [] := by intro start; simp [renderForest]
  have cons : ∀ left right leftRest rightRest
      (head : Laws.SameShape (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right)
      (tail : Laws.SameForest (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) leftRest rightRest),
      P left right → Q leftRest rightRest → Q (left :: leftRest) (right :: rightRest) := by
    intro left right leftRest rightRest head tail related continued start
    obtain ⟨next, root, nodes⟩ := related start
    have following := continued (renderAt right start).next
    simp only [renderForest]
    rw [next]
    refine ⟨following.1, ?_, ?_⟩
    · rw [root, following.2.1]
    · rw [nodes, following.2.2]
  constructor
  · intro left right shape
    exact Laws.SameShape.rec (motive_1 := fun l r _ => P l r)
      (motive_2 := fun ls rs _ => Q ls rs) empty node nil cons shape
  · intro left right shape
    exact Laws.SameForest.rec (motive_1 := fun l r _ => P l r)
      (motive_2 := fun ls rs _ => Q ls rs) empty node nil cons shape

theorem render_same_shape {Left Right : Type} (left : Ui Left) (right : Ui Right)
    (shape : Laws.SameShape (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right)
    (start : Nat) :
    (renderAt left start).next = (renderAt right start).next ∧
    (renderAt left start).root = (renderAt right start).root ∧
    (renderAt left start).nodes = (renderAt right start).nodes :=
  render_shape_all.1 left right shape start

theorem forest_same_shape {Left Right : Type} (left : List (Ui Left)) (right : List (Ui Right))
    (shape : Laws.SameForest (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right)
    (start : Nat) :
    (renderForest left start).next = (renderForest right start).next ∧
    (renderForest left start).roots = (renderForest right start).roots ∧
    (renderForest left start).nodes = (renderForest right start).nodes :=
  render_shape_all.2 left right shape start

theorem compile_same_shape {Left Right : Type} :
    Laws.shapeContract (@Attributes.renderProperties Left) (@Attributes.renderProperties Right)
      (@compile Left) (@compile Right) := by
  intro left right shape
  obtain ⟨_, root, nodes⟩ := render_same_shape left right shape 0
  apply View.scene_eq_of_fields
  · exact root
  · change Std.ExtTreeMap.ofList (renderAt left 0).nodes = Std.ExtTreeMap.ofList (renderAt right 0).nodes
    rw [nodes]

end Kotlean.Ui
