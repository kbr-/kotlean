import Kotlean.View.SceneProofs

namespace Kotlean.View.Canonical

open Kotlean Kotlean.View

def preorder (nodes : Std.ExtTreeMap Nat Node) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, id =>
    match nodes[id]? with
    | none => []
    | some node => id :: node.children.flatMap (preorder nodes fuel)

theorem preorder_equations (nodes : Std.ExtTreeMap Nat Node) (id : Nat) :
    preorder nodes 0 id = [] ∧ ∀ (fuel : Nat),
      preorder nodes (fuel + 1) id = match (nodes[id]? : Option Node) with
        | none => []
        | some node => id :: node.children.flatMap (preorder nodes fuel) := by
  exact ⟨rfl, fun _ => rfl⟩

def valid (state : Scene) : Prop :=
  let entries := state.nodes.toList
  let count := entries.length
  entries.map Prod.fst = List.range count ∧
  state.root = (if count = 0 then none else some 0) ∧
  (∀ entry ∈ entries,
    Kotlean.View.Laws.capacity entry.2.kind entry.2.children.length ∧
    ∀ child ∈ entry.2.children, entry.1 < child ∧ (state.nodes[child]?).isSome = true) ∧
  (∀ child ∈ (List.range count).drop 1,
    (entries.flatMap (fun entry => entry.2.children)).count child = 1) ∧
  preorder state.nodes count 0 = List.range count

instance (state : Scene) : Decidable (valid state) := by
  unfold valid
  infer_instance

theorem infix_flatMap_of_mem {α β : Type} (f : α → List β) (items : List α) (item : α)
    (h : item ∈ items) : (f item).IsInfix (items.flatMap f) := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem h
  simp [List.flatMap_append]

theorem first_child_adjacent (nodes : Std.ExtTreeMap Nat Node) (count : Nat)
    (graph : ∀ (parent : Nat) (node : Node), nodes[parent]? = some node → ∀ child ∈ node.children,
      parent < child ∧ child < count ∧ (nodes[child]?).isSome = true)
    (parent child : Nat) (node : Node) (rest : List Nat)
    (lookup : nodes[parent]? = some node) (first : node.children = child :: rest)
    (fuel start : Nat) (bound : count ≤ fuel + start)
    (member : parent ∈ preorder nodes fuel start) :
    [parent, child].IsInfix (preorder nodes fuel start) := by
  induction fuel generalizing start with
  | zero => simp [preorder] at member
  | succ fuel ih =>
    cases hs : nodes[start]? with
    | none => simp [preorder, hs] at member
    | some top =>
      simp only [preorder, hs, List.mem_cons] at member
      rcases member with he | member
      · subst start
        have ht : top = node := Option.some.inj (hs.symm.trans lookup)
        subst top
        have edge := graph parent node lookup child (by simp [first])
        cases fuel with
        | zero => omega
        | succ fuel =>
          cases hc : nodes[child]? with
          | none => simp [hc] at edge
          | some childNode =>
            refine ⟨[], childNode.children.flatMap (preorder nodes fuel) ++
              rest.flatMap (preorder nodes (fuel + 1)), ?_⟩
            simp [preorder, lookup, first, hc]
      · obtain ⟨descendant, hd, hm⟩ := List.mem_flatMap.mp member
        have edge := graph start top hs descendant hd
        have hb : count ≤ fuel + descendant := by omega
        have sub := ih descendant hb hm
        have embedded := infix_flatMap_of_mem (preorder nodes fuel) top.children descendant hd
        simpa only [preorder, hs] using List.infix_cons (sub.trans embedded)

theorem adjacent_range (parent child count : Nat) (h : [parent, child].IsInfix (List.range count)) :
    child = parent + 1 := by
  obtain ⟨before, after, h⟩ := h
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_range] at hl
  have hp : (List.range count)[before.length]? = some parent := by
    rw [← h, List.append_assoc, List.getElem?_append_right (by omega)]
    simp
  have hc : (List.range count)[before.length + 1]? = some child := by
    rw [← h, List.append_assoc, List.getElem?_append_right (by omega)]
    simp
  have bp : before.length < count := by omega
  have bc : before.length + 1 < count := by omega
  have ep : before.length = parent := by simpa [bp] using hp
  have ec : before.length + 1 = child := by simpa [bc] using hc
  omega


theorem valid_node_bound (state : Scene) (validity : valid state) (id : Nat) (node : Node)
    (lookup : state.nodes[id]? = some node) : id < state.nodes.toList.length := by
  have member : (id, node) ∈ state.nodes.toList :=
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr lookup
  have key : id ∈ state.nodes.toList.map Prod.fst := List.mem_map.mpr ⟨(id, node), member, rfl⟩
  rw [validity.1] at key
  exact List.mem_range.mp key

theorem valid_graph (state : Scene) (validity : valid state) :
    ∀ (parent : Nat) (node : Node), state.nodes[parent]? = some node → ∀ child ∈ node.children,
      parent < child ∧ child < state.nodes.toList.length ∧ (state.nodes[child]?).isSome = true := by
  intro parent node lookup child hc
  have member : (parent, node) ∈ state.nodes.toList :=
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr lookup
  have edge := (validity.2.2.1 (parent, node) member).2 child hc
  refine ⟨edge.1, ?_, edge.2⟩
  cases hl : state.nodes[child]? with
  | none => simp [hl] at edge
  | some node => exact valid_node_bound state validity child node hl

theorem valid_first_child (state : Scene) (validity : valid state)
    (parent child : Nat) (node : Node) (rest : List Nat)
    (lookup : state.nodes[parent]? = some node) (first : node.children = child :: rest) :
    child = parent + 1 := by
  have member : parent ∈ preorder state.nodes state.nodes.toList.length 0 := by
    rw [validity.2.2.2.2]
    exact List.mem_range.mpr (valid_node_bound state validity parent node lookup)
  have adjacent := first_child_adjacent state.nodes state.nodes.toList.length
    (valid_graph state validity) parent child node rest lookup first
    state.nodes.toList.length 0 (by omega) member
  rw [validity.2.2.2.2] at adjacent
  exact adjacent_range parent child state.nodes.toList.length adjacent

theorem valid_scroll_children (state : Scene) (validity : valid state) (id : Nat) (node : Node)
    (lookup : state.nodes[id]? = some node) (kind : node.kind = .scroll) :
    node.children = [] ∨ node.children = [id + 1] := by
  have member : (id, node) ∈ state.nodes.toList :=
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr lookup
  have capacity := (validity.2.2.1 (id, node) member).1
  have bound : node.children.length ≤ 1 := by
    simpa [Kotlean.View.Laws.capacity, kind] using capacity
  cases hc : node.children with
  | nil => exact Or.inl rfl
  | cons child rest =>
    have first := valid_first_child state validity id child node rest lookup hc
    have empty : rest = [] := by
      cases rest <;> simp_all
    exact Or.inr (by simp [first, empty])


end Kotlean.View.Canonical
