module
public import Kotlean.Ui.Handlers

@[expose] public section

namespace Kotlean.Ui

def nodeChunk {Msg : Type} (start : Nat) (kind : NodeKind) (attributes : Attributes Msg)
    (forest : Forest Msg) : Chunk Msg :=
  { next := forest.next, root := some start,
    nodes := (start, { kind := kind, properties := attributes.renderProperties, children := forest.roots }) :: forest.nodes,
    handlers := (start, attributes.events) :: forest.handlers }

def singleForest {Msg : Type} (chunk : Chunk Msg) : Forest Msg :=
  { next := chunk.next, roots := chunk.root.toList, nodes := chunk.nodes, handlers := chunk.handlers }

mutual
  def renderAt {Msg : Type} (tree : Ui Msg) (start : Nat) : Chunk Msg :=
    match tree with
    | .empty => { next := start }
    | .column attributes children => nodeChunk start .column attributes (renderForest children (start + 1))
    | .row attributes children => nodeChunk start .row attributes (renderForest children (start + 1))
    | .text attributes => nodeChunk start .text attributes { next := start + 1 }
    | .button attributes => nodeChunk start .button attributes { next := start + 1 }
    | .input attributes => nodeChunk start .input attributes { next := start + 1 }
    | .scroll attributes child => nodeChunk start .scroll attributes (singleForest (renderAt child (start + 1)))
    | .canvas attributes => nodeChunk start .canvas attributes { next := start + 1 }
  termination_by sizeOf tree
  decreasing_by all_goals simp_wf <;> omega

  def renderForest {Msg : Type} (trees : List (Ui Msg)) (start : Nat) : Forest Msg :=
    match trees with
    | [] => { next := start }
    | tree :: rest =>
      let first := renderAt tree start
      let following := renderForest rest first.next
      { next := following.next, roots := first.root.toList ++ following.roots,
        nodes := first.nodes ++ following.nodes, handlers := first.handlers ++ following.handlers }
  termination_by sizeOf trees
  decreasing_by all_goals simp_wf <;> omega
end

def compile {Msg : Type} (tree : Ui Msg) : Rendered Msg :=
  let chunk := renderAt tree 0
  { scene := { nodes := Std.ExtTreeMap.ofList chunk.nodes, root := chunk.root },
    handlers := Std.ExtTreeMap.ofList chunk.handlers }

theorem singleForest_layout {Msg : Type} (tree : Ui Msg) (start : Nat) (chunk : Chunk Msg)
    (layout : Laws.Layout (@Attributes.renderProperties Msg) tree start chunk) :
    Laws.ForestLayout (@Attributes.renderProperties Msg) [tree] start (singleForest chunk) := by
  simpa only [singleForest, List.append_nil] using
    Laws.ForestLayout.cons tree [] start chunk { next := chunk.next } layout (Laws.ForestLayout.nil chunk.next)

mutual
  theorem renderAt_layout {Msg : Type} (tree : Ui Msg) (start : Nat) :
      Laws.Layout (@Attributes.renderProperties Msg) tree start (renderAt tree start) := by
    cases tree with
    | empty =>
      simp only [renderAt]
      exact Laws.Layout.empty start
    | column attributes children =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .column attributes children (.column attributes children) start _
        (renderForest_layout children (start + 1))
    | row attributes children =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .row attributes children (.row attributes children) start _
        (renderForest_layout children (start + 1))
    | text attributes =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .text attributes [] (.text attributes) start _ (Laws.ForestLayout.nil (start + 1))
    | button attributes =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .button attributes [] (.button attributes) start _ (Laws.ForestLayout.nil (start + 1))
    | input attributes =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .input attributes [] (.input attributes) start _ (Laws.ForestLayout.nil (start + 1))
    | scroll attributes child =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .scroll attributes [child] (.scroll attributes child) start _
        (singleForest_layout child (start + 1) _ (renderAt_layout child (start + 1)))
    | canvas attributes =>
      simp only [renderAt, nodeChunk]
      exact Laws.Layout.node _ .canvas attributes [] (.canvas attributes) start _ (Laws.ForestLayout.nil (start + 1))
  termination_by sizeOf tree
  decreasing_by all_goals simp_wf <;> omega

  theorem renderForest_layout {Msg : Type} (trees : List (Ui Msg)) (start : Nat) :
      Laws.ForestLayout (@Attributes.renderProperties Msg) trees start (renderForest trees start) := by
    cases trees with
    | nil =>
      simp only [renderForest]
      exact Laws.ForestLayout.nil start
    | cons tree rest =>
      simp only [renderForest]
      exact Laws.ForestLayout.cons tree rest start _ _ (renderAt_layout tree start)
        (renderForest_layout rest (renderAt tree start).next)
  termination_by sizeOf trees
  decreasing_by all_goals simp_wf <;> omega
end

theorem compile_layout {Msg : Type} :
    Laws.layoutContract (@Attributes.renderProperties Msg) (@compile Msg) := by
  intro tree
  exact ⟨renderAt tree 0, renderAt_layout tree 0, rfl, rfl⟩

theorem form_capacity {Msg : Type} (tree : Ui Msg) (kind : NodeKind) (attributes : Attributes Msg)
    (children : List (Ui Msg)) (form : Laws.NodeForm tree kind attributes children) :
    View.Laws.capacity kind children.length := by
  cases form <;> simp [View.Laws.capacity]

end Kotlean.Ui
