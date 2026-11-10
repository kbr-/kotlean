module
public import Kotlean.View.Scene

@[expose] public section

namespace Kotlean.View.Laws

def capacity (kind : NodeKind) (count : Nat) : Prop :=
  match kind with
  | .column | .row => True
  | .scroll => count ≤ 1
  | .text | .button | .input | .canvas => count = 0

instance (kind : NodeKind) (count : Nat) : Decidable (capacity kind count) := by
  cases kind <;> simp only [capacity] <;> infer_instance

def withoutChild (child : Nat) (node : Node) : Node :=
  { node with children := node.children.filter (· ≠ child) }

def atIndex (index child : Nat) (children : List Nat) : List Nat :=
  children.take index ++ child :: children.drop index

def creation (step : Patch → Scene → Option Scene) : Prop :=
  ∀ state id kind,
    if state.nodes[id]? = none then
      ∃ result, step (.create id kind) state = some result ∧ result.root = state.root ∧
        ∀ key, result.nodes[key]? =
          if key = id then some { kind := kind } else state.nodes[key]?
    else step (.create id kind) state = none

def propertyChange (step : Patch → Scene → Option Scene)
    (apply : Property → Properties → Properties) : Prop :=
  ∀ state id property,
    match state.nodes[id]? with
    | none => step (.property id property) state = none
    | some node => ∃ result, step (.property id property) state = some result ∧
        result.root = state.root ∧ ∀ key, result.nodes[key]? =
          if key = id then some { node with properties := apply property node.properties }
          else state.nodes[key]?

def removal (step : Patch → Scene → Option Scene) : Prop :=
  ∀ state id,
    if state.nodes[id]? = none then step (.remove id) state = none
    else ∃ result, step (.remove id) state = some result ∧
      result.root = (if state.root = some id then none else state.root) ∧
      ∀ key, result.nodes[key]? =
        if key = id then none else (state.nodes[key]?).map (withoutChild id)

def insertion (step : Patch → Scene → Option Scene) : Prop :=
  ∀ state parent index child,
    match state.nodes[parent]?, state.nodes[child]? with
    | some node, some _ =>
      let remaining := (withoutChild child node).children
      if parent < child ∧ index ≤ remaining.length ∧ capacity node.kind (remaining.length + 1)
      then ∃ result, step (.insert parent index child) state = some result ∧
        result.root = state.root ∧ ∀ key, result.nodes[key]? =
          if key = parent then some { node with children := atIndex index child remaining }
          else (state.nodes[key]?).map (withoutChild child)
      else step (.insert parent index child) state = none
    | _, _ => step (.insert parent index child) state = none

def rootSelection (step : Patch → Scene → Option Scene) : Prop :=
  ∀ (state : Scene) (root : Option Nat),
    if root.all (fun id => state.nodes[id]?.isSome) then
      ∃ result, step (.root root) state = some result ∧
        result.root = root ∧ ∀ (key : Nat), result.nodes[key]? = state.nodes[key]?
    else step (.root root) state = none

end Kotlean.View.Laws

namespace Kotlean.View.Proofs

open Kotlean Kotlean.View Kotlean.View.Laws

theorem capacity_agrees (kind : NodeKind) (count : Nat) :
    childCapacity kind count = true ↔ capacity kind count := by
  cases kind <;> simp [childCapacity, capacity]

theorem create_verified : creation applyPatch := by
  intro state id kind
  split
  next h =>
    refine ⟨{ state with nodes := state.nodes.insert id { kind := kind } }, ?_, rfl, ?_⟩
    · simp [applyPatch, h]
    · intro key
      exact lookup_insert _ _ _ _
  next h =>
    cases hv : state.nodes[id]? with
    | none => exact False.elim (h hv)
    | some node => simp [applyPatch, hv]

theorem property_verified : propertyChange applyPatch applyProperty := by
  intro state id property
  cases h : state.nodes[id]? with
  | none => simp [applyPatch, h]
  | some node =>
    let updated : Node := { node with properties := applyProperty property node.properties }
    refine ⟨{ state with nodes := state.nodes.insert id updated }, ?_, rfl, ?_⟩
    · simp [applyPatch, h, updated]
    · intro key
      exact lookup_insert _ _ _ _

theorem remove_verified : removal applyPatch := by
  intro state id
  split
  next h => simp [applyPatch, h]
  next h =>
    refine ⟨{ nodes := (state.nodes.erase id).map (fun _ => detachChild id)
              root := if state.root = some id then none else state.root }, ?_, rfl, ?_⟩
    · cases hv : state.nodes[id]? with
      | none => exact False.elim (h hv)
      | some node => simp [applyPatch, hv]
    · intro key
      exact lookup_remove _ _ _

theorem insert_verified : insertion applyPatch := by
  intro state parent index child
  cases hp : state.nodes[parent]? with
  | none => simp [applyPatch, hp]
  | some node =>
    cases hc : state.nodes[child]? with
    | none => simp [applyPatch, hp, hc]
    | some childNode =>
      dsimp
      split
      next h =>
        let updated : Node :=
          { node with children := insertChild index child (detachChild child node).children }
        let nodes := (state.nodes.map (fun _ => detachChild child)).insert parent updated
        refine ⟨{ state with nodes := nodes }, ?_, rfl, ?_⟩
        · change parent < child ∧ index ≤ (detachChild child node).children.length ∧
            capacity node.kind ((detachChild child node).children.length + 1) at h
          simp [applyPatch, hp, hc, h.1, h.2.1, (capacity_agrees _ _).mpr h.2.2, nodes, updated]
        · intro key
          dsimp [nodes, updated]
          rw [lookup_insert]
          split
          · rfl
          · exact lookup_detach _ _ _
      next h =>
        change ¬(parent < child ∧ index ≤ (detachChild child node).children.length ∧
          capacity node.kind ((detachChild child node).children.length + 1)) at h
        simp_all [applyPatch, Bool.and_eq_true, capacity_agrees]

theorem root_verified : rootSelection applyPatch := by
  intro state root
  split
  next h => exact ⟨{ state with root := root }, by simp only [applyPatch, h, ↓reduceIte], rfl, fun _ => rfl⟩
  next h =>
    change (if root.all (fun id => state.nodes[id]?.isSome) then _ else none) = none
    split
    · next ht => exact False.elim (h ht)
    · rfl

end Kotlean.View.Proofs

