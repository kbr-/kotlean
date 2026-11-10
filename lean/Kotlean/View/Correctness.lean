import Kotlean.View.Canonical
import Kotlean.View.Attachments

namespace Kotlean.View.DiffProofs

open Kotlean Kotlean.View Kotlean.View.Canonical Kotlean.View.Attachments

theorem mem_scene_plan (state : Scene) (parent child : Nat) :
    (parent, child) ∈ edgePlan state.nodes.toList ↔
      ∃ node, state.nodes[parent]? = some node ∧ child ∈ node.children := by
  rw [mem_edgePlan]
  simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

theorem scene_plan_nodup (state : Scene) (validity : valid state) :
    (moved (edgePlan state.nodes.toList)).Nodup := by
  apply List.nodup_iff_count_of_mem.mpr
  intro child member
  obtain ⟨⟨parent, value⟩, hm, he⟩ := List.mem_map.mp member
  dsimp at he
  subst value
  obtain ⟨node, lookup, hc⟩ := (mem_scene_plan state parent child).mp hm
  have edge := valid_graph state validity parent node lookup child hc
  have nonroot : child ∈ (List.range state.nodes.toList.length).drop 1 := by
    simp only [List.range_eq_range', List.drop_range', List.mem_range'_1]
    constructor <;> omega
  rw [moved_edgePlan]
  exact validity.2.2.2.1 child nonroot

theorem split_fresh (state : Scene) (validity : valid state) (before after : List Edge)
    (parent child : Nat) (split : edgePlan state.nodes.toList = before ++ (parent, child) :: after) :
    child ∉ moved before := by
  have hd := scene_plan_nodup state validity
  rw [split] at hd
  unfold moved at hd
  rw [List.map_append, List.map_cons] at hd
  have apart := (List.nodup_append.mp hd).2.2
  intro hm
  exact apart child hm child (by simp) rfl

theorem prepared_scroll (old new : Scene) (validity : valid old) (id : Nat) (node : Node)
    (lookup : (preparedScene old new).nodes[id]? = some node) (kind : node.kind = .scroll) :
    node.children = [] ∨ node.children = [id + 1] := by
  cases hn : new.nodes[id]? with
  | none => simp [preparedScene, hn] at lookup
  | some target =>
    simp only [preparedScene, Std.ExtTreeMap.getElem?_map, hn, Option.map_some, Option.some.injEq] at lookup
    subst node
    change target.kind = .scroll at kind
    cases ho : old.nodes[id]? with
    | none => simp [remainingNode, ho]
    | some before =>
      by_cases hk : before.kind = target.kind
      · have hm : id ∉ removedIds old new := by simp [mem_removedIds, sameKind, ho, hn, hk]
        have hs := valid_scroll_children old validity id before ho (hk.trans kind)
        rcases hs with hs | hs
        · simp [remainingNode, hm, ho, withoutChildren, hs]
        · by_cases hc : id + 1 ∈ removedIds old new <;>
            simp [remainingNode, hm, ho, withoutChildren, hs, hc]
      · have hm : id ∈ removedIds old new := by simp [mem_removedIds, sameKind, ho, hn, hk]
        simp [remainingNode, hm]


def preparedRecord (old new : Scene) (id : Nat) (target : Node) : Node :=
  { target with children := ((remainingNode old new id).map Node.children).getD [] }

theorem prepared_lookup (old new : Scene) (id : Nat) (target : Node)
    (lookup : new.nodes[id]? = some target) :
    (preparedScene old new).nodes[id]? = some (preparedRecord old new id target) := by
  simp [preparedScene, preparedRecord, lookup]

theorem plan_safe (old new : Scene) (vo : valid old) (vn : valid new)
    (before after : List Edge) (parent child : Nat)
    (split : edgePlan new.nodes.toList = before ++ (parent, child) :: after) :
    safeEdge (preparedScene old new) before (parent, child) := by
  have member : (parent, child) ∈ edgePlan new.nodes.toList := by rw [split]; simp
  obtain ⟨target, hp, hc⟩ := (mem_scene_plan new parent child).mp member
  have edge := valid_graph new vn parent target hp child hc
  have fresh := split_fresh new vn before after parent child split
  cases hchild : new.nodes[child]? with
  | none => simp [hchild] at edge
  | some childTarget =>
    refine ⟨preparedRecord old new parent target, preparedRecord old new child childTarget,
      prepared_lookup old new parent target hp, prepared_lookup old new child childTarget hchild,
      edge.1, fresh, ?_⟩
    have cap := (vn.2.2.1 (parent, target)
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hp)).1
    change childCapacity target.kind
      ((detachChild child (attachmentNode before parent (preparedRecord old new parent target))).children.length + 1) = true
    cases kind : target.kind
    case column => simp [childCapacity]
    case row => simp [childCapacity]
    case scroll =>
      have targetShape := valid_scroll_children new vn parent target hp kind
      have targetChildren : target.children = [child] := by
        rcases targetShape with he | he
        · simp [he] at hc
        · have hid : child = parent + 1 := by simpa [he] using hc
          simpa [hid] using he
      have hid : child = parent + 1 := by
        exact valid_first_child new vn parent child target [] hp targetChildren
      have clear : targets before parent = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value hm
        have hb : (parent, value) ∈ before := (mem_targets before parent value).mp hm
        have hm' : (parent, value) ∈ edgePlan new.nodes.toList := by rw [split]; simp [hb]
        obtain ⟨same, hs, hv⟩ := (mem_scene_plan new parent value).mp hm'
        have he : same = target := Option.some.inj (hs.symm.trans hp)
        subst same
        have hv' : value = child := by simpa [targetChildren] using hv
        subst value
        exact fresh (List.mem_map.mpr ⟨(parent, child), hb, rfl⟩)
      have baseShape := prepared_scroll old new vo parent (preparedRecord old new parent target)
        (prepared_lookup old new parent target hp) (by simpa [preparedRecord] using kind)
      have shape : (preparedRecord old new parent target).children = [] ∨
          (preparedRecord old new parent target).children = [child] := by
        simpa [hid] using baseShape
      have empty : (detachChild child (attachmentNode before parent
          (preparedRecord old new parent target))).children = [] := by
        rcases shape with he | he <;>
          simp [attachmentNode, clear, withoutChildren, detachChild, he, fresh]
      simp [childCapacity, empty]
    all_goals
      simp [Kotlean.View.Laws.capacity, kind] at cap
      simp [cap] at hc

theorem childPhase_exact (old new : Scene) (vo : valid old) (vn : valid new) :
    applyPatches (childPatches new.nodes.toList) (preparedScene old new) =
      some (attachmentStage (preparedScene old new) (edgePlan new.nodes.toList)) := by
  have hd : (new.nodes.toList.map Prod.fst).Nodup := by simpa using new.nodes.nodup_keys
  have patches := childPatches_plan new.nodes.toList [] hd (by intro entry _; rfl)
  have result := attachmentFold_apply (preparedScene old new) [] (edgePlan new.nodes.toList)
    (by intro before edge after he; exact plan_safe old new vo vn before after edge.1 edge.2 he)
  simpa only [List.nil_append, attachmentStage_nil, patches] using result


theorem nonroot_in_plan (state : Scene) (validity : valid state) (id : Nat) (node : Node)
    (lookup : state.nodes[id]? = some node) (positive : 0 < id) :
    id ∈ moved (edgePlan state.nodes.toList) := by
  have bound := valid_node_bound state validity id node lookup
  have nonroot : id ∈ (List.range state.nodes.toList.length).drop 1 := by
    simp only [List.range_eq_range', List.drop_range', List.mem_range'_1]
    constructor <;> omega
  have count := validity.2.2.2.1 id nonroot
  by_cases member : id ∈ moved (edgePlan state.nodes.toList)
  · exact member
  · have zero := List.count_eq_zero.mpr member
    rw [moved_edgePlan] at zero
    omega

theorem child_survives (old new : Scene) (id : Nat) (present : (old.nodes[id]?).isSome = true)
    (retained : id ∉ removedIds old new) : (new.nodes[id]?).isSome = true := by
  cases ho : old.nodes[id]? with
  | none => simp [ho] at present
  | some before =>
    cases hn : new.nodes[id]? with
    | none =>
      have removed : id ∈ removedIds old new := by simp [mem_removedIds, sameKind, ho, hn]
      exact False.elim (retained removed)
    | some target => simp

theorem prepared_child_source (old new : Scene) (parent child : Nat) (target : Node)
    (member : child ∈ (preparedRecord old new parent target).children) :
    ∃ before, old.nodes[parent]? = some before ∧ child ∈ before.children ∧ child ∉ removedIds old new := by
  by_cases removed : parent ∈ removedIds old new
  · simp [preparedRecord, remainingNode, removed] at member
  · cases ho : old.nodes[parent]? with
    | none => simp [preparedRecord, remainingNode, removed, ho] at member
    | some before =>
      have h := member
      simp only [preparedRecord, remainingNode, removed, ↓reduceIte, ho, Option.map_some, Option.getD_some,
        withoutChildren, List.mem_filter, decide_eq_true_eq] at h
      exact ⟨before, rfl, h⟩

theorem prepared_children_covered (old new : Scene) (vo : valid old) (vn : valid new)
    (parent : Nat) (target : Node) :
    ∀ child ∈ (preparedRecord old new parent target).children, child ∈ moved (edgePlan new.nodes.toList) := by
  intro child member
  obtain ⟨before, hp, hc, retained⟩ := prepared_child_source old new parent child target member
  have edge := valid_graph old vo parent before hp child hc
  have surviving := child_survives old new child edge.2.2 retained
  cases hn : new.nodes[child]? with
  | none => simp [hn] at surviving
  | some node => exact nonroot_in_plan new vn child node hn (by omega)

theorem attachmentStage_final (old new : Scene) (vo : valid old) (vn : valid new) :
    attachmentStage (preparedScene old new) (edgePlan new.nodes.toList) =
      { new with root := (preparedScene old new).root } := by
  apply scene_eq_of_fields
  · rfl
  · apply Std.ExtTreeMap.ext_getElem?
    intro key
    cases hn : new.nodes[key]? with
    | none => simp [attachmentStage, preparedScene, hn]
    | some target =>
      simp only [attachmentStage, Std.ExtTreeMap.getElem?_map,
        prepared_lookup old new key target hn, Option.map_some]
      apply congrArg some
      have hd : (new.nodes.toList.map Prod.fst).Nodup := by simpa using new.nodes.nodup_keys
      have ht := targets_edgePlan new.nodes.toList key target hd
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hn)
      have hf : (withoutChildren (moved (edgePlan new.nodes.toList))
          (preparedRecord old new key target)).children = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro child hc
        have moved := prepared_children_covered old new vo vn key target child hc
        simp [moved]
      simp only [attachmentNode, ht, hf, List.append_nil]
      rfl


theorem valid_root_ready (state : Scene) (validity : valid state) :
    state.root.all (fun id => (state.nodes[id]?).isSome) = true := by
  rw [validity.2.1]
  by_cases empty : state.nodes.toList.length = 0
  · simp [empty]
  · simp only [empty, ↓reduceIte]
    change (state.nodes[0]?).isSome = true
    have key : 0 ∈ state.nodes.toList.map Prod.fst := by
      rw [validity.1]
      exact List.mem_range.mpr (Nat.pos_of_ne_zero empty)
    have present : 0 ∈ state.nodes := by simpa using key
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mp present

theorem diffScene_correct (old new : Scene) (vo : valid old) (vn : valid new) :
    applyPatches (diffScene old new) old = some new := by
  by_cases hs : sceneStructure old = sceneStructure new
  · exact diffScene_propertyApplication old new hs
  · have he : sceneObservation old ≠ sceneObservation new := by
      intro same
      have equal := sameObservation_eq old new same
      subst new
      exact hs rfl
    have sequence : diffScene old new =
        (removedNodePatches old new ++ new.nodes.toList.flatMap (fun (id, node) => nodePatches old id node)) ++
          (childPatches new.nodes.toList ++ [.root new.root]) := by
      simp [diffScene, he, hs, List.append_assoc]
    rw [sequence, applyPatches_append, preparation_exact]
    simp only [Option.bind_some]
    rw [applyPatches_append, childPhase_exact old new vo vn]
    simp only [Option.bind_some]
    rw [attachmentStage_final old new vo vn]
    simp only [applyPatches_cons, applyPatch, valid_root_ready new vn, ↓reduceIte,
      Option.bind_some, applyPatches_nil]



end Kotlean.View.DiffProofs

namespace Kotlean.View

theorem diffScene_correct (old new : Scene) (vo : Canonical.valid old) (vn : Canonical.valid new) :
    applyPatches (diffScene old new) old = some new :=
  DiffProofs.diffScene_correct old new vo vn

end Kotlean.View
