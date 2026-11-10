import Kotlean.View.Application

namespace Kotlean.View.Attachments

open Kotlean Kotlean.View

abbrev Edge := Nat × Nat

def targets (doneEdges : List Edge) (parent : Nat) : List Nat :=
  doneEdges.filterMap (fun (owner, child) => if owner = parent then some child else none)

def moved (doneEdges : List Edge) : List Nat := doneEdges.map Prod.snd

theorem targets_append (doneEdges : List Edge) (parent child key : Nat) :
    targets (doneEdges ++ [(parent, child)]) key =
      targets doneEdges key ++ if parent = key then [child] else [] := by
  by_cases he : parent = key <;>
    simp [targets, List.filterMap_append, he]

theorem mem_targets (doneEdges : List Edge) (parent child : Nat) :
    child ∈ targets doneEdges parent ↔ (parent, child) ∈ doneEdges := by
  constructor
  · intro h
    obtain ⟨⟨owner, value⟩, hm, hv⟩ := List.mem_filterMap.mp h
    dsimp at hv
    split at hv
    · next he => simp_all
    · simp at hv
  · intro h
    exact List.mem_filterMap.mpr ⟨(parent, child), h, by simp⟩

theorem targets_fresh (doneEdges : List Edge) (parent child : Nat) (fresh : child ∉ moved doneEdges) :
    (targets doneEdges parent).filter (· ≠ child) = targets doneEdges parent := by
  apply List.filter_eq_self.mpr
  intro value hm
  have hn : value ≠ child := by
    intro he
    subst value
    exact fresh (List.mem_map.mpr ⟨(parent, child), (mem_targets doneEdges parent child).mp hm, rfl⟩)
  simpa using hn

theorem withoutChildren_append (doneEdges : List Edge) (parent child : Nat) (node : Node) :
    withoutChildren (moved (doneEdges ++ [(parent, child)])) node =
      detachChild child (withoutChildren (moved doneEdges) node) := by
  have hm : moved (doneEdges ++ [(parent, child)]) = moved doneEdges ++ [child] := by
    unfold moved
    rw [List.map_append]
    rfl
  rw [hm]
  cases node
  simp [withoutChildren, detachChild, List.filter_filter, Bool.and_comm]

def attachmentNode (doneEdges : List Edge) (parent : Nat) (node : Node) : Node :=
  { node with children := targets doneEdges parent ++ (withoutChildren (moved doneEdges) node).children }

def attachmentStage (state : Scene) (doneEdges : List Edge) : Scene :=
  { state with nodes := state.nodes.map (attachmentNode doneEdges) }

theorem insertChild_after_prefix (before after : List Nat) (child : Nat) :
    insertChild before.length child (before ++ after) = before ++ child :: after := by
  simp [insertChild]

theorem attachmentNode_append_other (doneEdges : List Edge) (parent child key : Nat) (node : Node)
    (other : key ≠ parent) (fresh : child ∉ moved doneEdges) :
    attachmentNode (doneEdges ++ [(parent, child)]) key node =
      detachChild child (attachmentNode doneEdges key node) := by
  simp only [attachmentNode, targets_append, Ne.symm other, ↓reduceIte, List.append_nil, withoutChildren_append,
    detachChild, List.filter_append, targets_fresh doneEdges key child fresh]

theorem attachmentNode_append_parent (doneEdges : List Edge) (parent child : Nat) (node : Node)
    (fresh : child ∉ moved doneEdges) :
    attachmentNode (doneEdges ++ [(parent, child)]) parent node =
      { node with children := insertChild (targets doneEdges parent).length child (
        (detachChild child (attachmentNode doneEdges parent node)).children) } := by
  simp only [attachmentNode, targets_append, ↓reduceIte, withoutChildren_append,
    detachChild, List.filter_append, targets_fresh doneEdges parent child fresh,
    insertChild_after_prefix, List.append_assoc, List.cons_append, List.nil_append]


theorem attachment_step (state : Scene) (doneEdges : List Edge) (parent child : Nat)
    (node childNode : Node) (hp : state.nodes[parent]? = some node)
    (hc : state.nodes[child]? = some childNode) (below : parent < child)
    (fresh : child ∉ moved doneEdges)
    (capacity : childCapacity node.kind
      ((detachChild child (attachmentNode doneEdges parent node)).children.length + 1) = true) :
    applyPatch (.insert parent (targets doneEdges parent).length child) (attachmentStage state doneEdges) =
      some (attachmentStage state (doneEdges ++ [(parent, child)])) := by
  let before := attachmentStage state doneEdges
  have hp' : before.nodes[parent]? = some (attachmentNode doneEdges parent node) := by
    simp [before, attachmentStage, hp]
  have hc' : before.nodes[child]? = some (attachmentNode doneEdges child childNode) := by
    simp [before, attachmentStage, hc]
  have remaining : (detachChild child (attachmentNode doneEdges parent node)).children =
      targets doneEdges parent ++ (detachChild child (withoutChildren (moved doneEdges) node)).children := by
    simp only [attachmentNode, detachChild, List.filter_append, targets_fresh doneEdges parent child fresh]
  have index : (targets doneEdges parent).length ≤
      (detachChild child (attachmentNode doneEdges parent node)).children.length := by
    rw [remaining, List.length_append]
    omega
  let children := insertChild (targets doneEdges parent).length child (
    (detachChild child (attachmentNode doneEdges parent node)).children)
  let updated : Node := { attachmentNode doneEdges parent node with children := children }
  have step : applyPatch (.insert parent (targets doneEdges parent).length child) before =
      some { before with nodes := (before.nodes.map (fun _ => detachChild child)).insert parent updated } := by
    have index' := index
    have capacity' := capacity
    dsimp only [attachmentNode] at index' capacity'
    simp [applyPatch, hp', hc', below, index', attachmentNode, capacity', updated, children]
  rw [step]
  apply congrArg some
  apply scene_eq_of_fields
  · rfl
  · apply Std.ExtTreeMap.ext_getElem?
    intro key
    rw [lookup_insert]
    by_cases he : key = parent
    · subst key
      simp only [↓reduceIte]
      simp only [attachmentStage, Std.ExtTreeMap.getElem?_map, hp, Option.map_some]
      exact congrArg some (attachmentNode_append_parent doneEdges parent child node fresh).symm
    · simp only [he, ↓reduceIte]
      rw [lookup_detach]
      cases hk : state.nodes[key]? with
      | none => simp [before, attachmentStage, hk]
      | some value =>
        simpa only [before, attachmentStage, Std.ExtTreeMap.getElem?_map, hk, Option.map_some] using
          congrArg some (attachmentNode_append_other doneEdges parent child key value he fresh).symm


def attachmentPatches (doneEdges : List Edge) : List Edge → List Patch
  | [] => []
  | (parent, child) :: rest =>
    .insert parent (targets doneEdges parent).length child ::
      attachmentPatches (doneEdges ++ [(parent, child)]) rest

def edgePlan (entries : List (Nat × Node)) : List Edge :=
  entries.flatMap (fun (parent, node) => node.children.map (parent, ·))

theorem targets_concat (first second : List Edge) (parent : Nat) :
    targets (first ++ second) parent = targets first parent ++ targets second parent := by
  exact List.filterMap_append

theorem targets_row (children : List Nat) (parent key : Nat) :
    targets (children.map (parent, ·)) key = if parent = key then children else [] := by
  by_cases he : parent = key
  · subst key
    induction children with
    | nil => simp [targets]
    | cons child rest ih =>
      simp only [targets, List.map_cons, List.filterMap_cons, ↓reduceIte] at ih ⊢
      rw [ih]
  · induction children with
    | nil => simp [targets, he]
    | cons child rest ih =>
      simp only [targets, List.map_cons, List.filterMap_cons, he, ↓reduceIte] at ih ⊢
      rw [ih]

theorem attachmentPatches_append (doneEdges first second : List Edge) :
    attachmentPatches doneEdges (first ++ second) =
      attachmentPatches doneEdges first ++ attachmentPatches (doneEdges ++ first) second := by
  induction first generalizing doneEdges with
  | nil => simp [attachmentPatches]
  | cons edge rest ih =>
    obtain ⟨parent, child⟩ := edge
    simp [attachmentPatches, ih, List.append_assoc]

theorem attachmentPatches_row (doneEdges : List Edge) (parent : Nat) (children : List Nat) :
    attachmentPatches doneEdges (children.map (parent, ·)) =
      children.mapIdx (fun index child => .insert parent ((targets doneEdges parent).length + index) child) := by
  induction children generalizing doneEdges with
  | nil => rfl
  | cons child rest ih =>
    simp [List.mapIdx_cons, attachmentPatches, ih, targets_append,
      Nat.add_assoc, Nat.add_comm]

theorem childPatches_plan (entries : List (Nat × Node)) (doneEdges : List Edge)
    (distinct : (entries.map Prod.fst).Nodup)
    (clear : ∀ entry ∈ entries, targets doneEdges entry.1 = []) :
    attachmentPatches doneEdges (edgePlan entries) = childPatches entries := by
  induction entries generalizing doneEdges with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨parent, node⟩ := entry
    have hd := List.nodup_cons.mp distinct
    have hz := clear (parent, node) (by simp)
    change attachmentPatches doneEdges
      (node.children.map (parent, ·) ++ edgePlan rest) =
      node.children.mapIdx (fun index child => .insert parent index child) ++ childPatches rest
    rw [attachmentPatches_append, attachmentPatches_row, hz]
    simp only [List.length_nil, Nat.zero_add]
    rw [ih _ hd.2]
    intro entry hm
    have hn : parent ≠ entry.1 := by
      intro he
      exact hd.1 (List.mem_map.mpr ⟨entry, hm, he.symm⟩)
    rw [targets_concat, targets_row]
    simp only [hn, ↓reduceIte, List.append_nil]
    exact clear entry (by simp [hm])


theorem attachmentNode_nil (key : Nat) (node : Node) : attachmentNode [] key node = node := by
  have hf : node.children.filter (fun _ => true) = node.children := List.filter_eq_self.mpr (by simp)
  simp [attachmentNode, targets, moved, withoutChildren, hf]

theorem attachmentStage_nil (state : Scene) : attachmentStage state [] = state := by
  apply scene_eq_of_fields
  · rfl
  · apply Std.ExtTreeMap.ext_getElem?
    intro key
    cases hk : state.nodes[key]? <;> simp [attachmentStage, hk, attachmentNode_nil]

def safeEdge (state : Scene) (doneEdges : List Edge) (edge : Edge) : Prop :=
  ∃ node childNode, state.nodes[edge.1]? = some node ∧ state.nodes[edge.2]? = some childNode ∧
    edge.1 < edge.2 ∧ edge.2 ∉ moved doneEdges ∧
    childCapacity node.kind
      ((detachChild edge.2 (attachmentNode doneEdges edge.1 node)).children.length + 1) = true

theorem attachmentFold_apply (state : Scene) (doneEdges rest : List Edge)
    (safe : ∀ before edge after, rest = before ++ edge :: after →
      safeEdge state (doneEdges ++ before) edge) :
    applyPatches (attachmentPatches doneEdges rest) (attachmentStage state doneEdges) =
      some (attachmentStage state (doneEdges ++ rest)) := by
  induction rest generalizing doneEdges with
  | nil => simp [attachmentPatches, applyPatches_nil]
  | cons edge rest ih =>
    obtain ⟨parent, child⟩ := edge
    have ready := safe [] (parent, child) rest (by simp)
    simp only [List.append_nil] at ready
    obtain ⟨node, childNode, hp, hc, below, fresh, capacity⟩ := ready
    rw [attachmentPatches, applyPatches_cons,
      attachment_step state doneEdges parent child node childNode hp hc below fresh capacity]
    simp only [Option.bind_some]
    rw [ih]
    · simp [List.append_assoc]
    · intro before edge after he
      have ready := safe ((parent, child) :: before) edge after (by simp [he])
      simpa only [List.append_assoc, List.singleton_append] using ready


theorem mem_edgePlan (entries : List (Nat × Node)) (parent child : Nat) :
    (parent, child) ∈ edgePlan entries ↔
      ∃ node, (parent, node) ∈ entries ∧ child ∈ node.children := by
  constructor
  · intro h
    obtain ⟨⟨owner, node⟩, hm, hc⟩ := List.mem_flatMap.mp h
    obtain ⟨value, hv, he⟩ := List.mem_map.mp hc
    cases he
    exact ⟨node, hm, hv⟩
  · rintro ⟨node, hm, hc⟩
    exact List.mem_flatMap.mpr ⟨(parent, node), hm, List.mem_map.mpr ⟨child, hc, rfl⟩⟩

theorem moved_edgePlan (entries : List (Nat × Node)) :
    moved (edgePlan entries) = entries.flatMap (fun entry => entry.2.children) := by
  simp [moved, edgePlan, List.map_flatMap, List.map_map, Function.comp_def]

theorem targets_edgePlan_absent (entries : List (Nat × Node)) (parent : Nat)
    (absent : parent ∉ entries.map Prod.fst) : targets (edgePlan entries) parent = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child hm
  have edge := (mem_targets (edgePlan entries) parent child).mp hm
  obtain ⟨node, hn, _⟩ := (mem_edgePlan entries parent child).mp edge
  exact absent (List.mem_map.mpr ⟨(parent, node), hn, rfl⟩)

theorem targets_edgePlan (entries : List (Nat × Node)) (parent : Nat) (node : Node)
    (distinct : (entries.map Prod.fst).Nodup) (member : (parent, node) ∈ entries) :
    targets (edgePlan entries) parent = node.children := by
  induction entries generalizing parent node with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨owner, top⟩ := entry
    have hd := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with he | hm
    · cases he
      change targets (node.children.map (parent, ·) ++ edgePlan rest) parent = node.children
      rw [targets_concat, targets_row, targets_edgePlan_absent rest parent hd.1]
      simp
    · have hn : owner ≠ parent := by
        intro he
        subst owner
        exact hd.1 (List.mem_map.mpr ⟨(parent, node), hm, rfl⟩)
      change targets (top.children.map (owner, ·) ++ edgePlan rest) parent = node.children
      rw [targets_concat, targets_row]
      simp only [hn, ↓reduceIte, List.nil_append]
      exact ih parent node hd.2 hm


end Kotlean.View.Attachments
