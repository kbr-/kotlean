import Kotlean.View.Scene

namespace Kotlean.View

def sceneObservation (state : Scene) : Option Nat × List (Nat × Node) :=
  (state.root, state.nodes.toList)

def sceneStructure (state : Scene) : Option Nat × List (Nat × NodeKind × List Nat) :=
  (state.root, state.nodes.toList.map (fun (id, node) => (id, node.kind, node.children)))

def sameKind (old new : Scene) (id : Nat) : Bool :=
  match old.nodes[id]?, new.nodes[id]? with
  | some before, some after => before.kind == after.kind
  | _, _ => false

def createNodePatches (id : Nat) (node : Node) : List Patch :=
  .create id node.kind :: (allProperties node.properties).map (.property id)

def nodePatches (old : Scene) (id : Nat) (node : Node) : List Patch :=
  match old.nodes[id]? with
  | some before =>
    if before.kind = node.kind then
      (diffProperties before.properties node.properties).map (.property id)
    else createNodePatches id node
  | none => createNodePatches id node

def removedNodePatches (old new : Scene) : List Patch :=
  old.nodes.toList.filterMap fun (id, _) =>
    if sameKind old new id then none else some (.remove id)

def childPatches (entries : List (Nat × Node)) : List Patch :=
  entries.flatMap fun (parent, node) =>
    node.children.mapIdx (fun index child => .insert parent index child)

def diffScene (old new : Scene) : List Patch :=
  if equal (sceneObservation old) (sceneObservation new) then []
  else
    removedNodePatches old new ++
    new.nodes.toList.flatMap (fun (id, node) => nodePatches old id node) ++
    if equal (sceneStructure old) (sceneStructure new) then []
    else childPatches new.nodes.toList ++ [.root new.root]

theorem diffScene_self (state : Scene) : diffScene state state = [] := by
  simp [diffScene]

theorem sameKind_of_survivor (old new : Scene) (id : Nat) (before after : Node)
    (ho : old.nodes[id]? = some before) (hn : new.nodes[id]? = some after)
    (hk : before.kind = after.kind) : sameKind old new id = true := by
  simp [sameKind, ho, hn, hk]

theorem remove_not_nodePatches (old : Scene) (id target : Nat) (node : Node) :
    Patch.remove target ∉ nodePatches old id node := by
  cases h : old.nodes[id]? with
  | none => simp [nodePatches, h, createNodePatches]
  | some before =>
    by_cases hk : before.kind = node.kind <;>
      simp [nodePatches, h, hk, createNodePatches]

theorem create_not_nodePatches_of_other (old : Scene) (id target : Nat) (node : Node)
    (kind : NodeKind) (h : id ≠ target) : Patch.create target kind ∉ nodePatches old id node := by
  cases ho : old.nodes[id]? with
  | none => simp [nodePatches, ho, createNodePatches, Ne.symm h]
  | some before =>
    by_cases hk : before.kind = node.kind <;>
      simp [nodePatches, ho, hk, createNodePatches, Ne.symm h]

theorem remove_not_children (entries : List (Nat × Node)) (id : Nat) :
    Patch.remove id ∉ childPatches entries := by
  simp [childPatches, List.mem_flatMap, List.mem_mapIdx]

theorem create_not_children (entries : List (Nat × Node)) (id : Nat) (kind : NodeKind) :
    Patch.create id kind ∉ childPatches entries := by
  simp [childPatches, List.mem_flatMap, List.mem_mapIdx]

theorem removedNodePatches_survivor (old new : Scene) (id : Nat)
    (h : sameKind old new id = true) : Patch.remove id ∉ removedNodePatches old new := by
  intro hm
  obtain ⟨⟨key, node⟩, _, hp⟩ := List.mem_filterMap.mp hm
  change (if sameKind old new key then none else some (Patch.remove key)) = some (.remove id) at hp
  split at hp
  · contradiction
  · cases hp
    simp_all

theorem create_not_removedNodePatches (old new : Scene) (id : Nat) (kind : NodeKind) :
    Patch.create id kind ∉ removedNodePatches old new := by
  intro hm
  obtain ⟨⟨key, node⟩, _, hp⟩ := List.mem_filterMap.mp hm
  change (if sameKind old new key then none else some (Patch.remove key)) = some (.create id kind) at hp
  split at hp <;> simp at hp

theorem diffScene_survivors (old new : Scene) (id : Nat) (before after : Node)
    (ho : old.nodes[id]? = some before) (hn : new.nodes[id]? = some after)
    (hk : before.kind = after.kind) :
    Patch.remove id ∉ diffScene old new ∧ ∀ kind, Patch.create id kind ∉ diffScene old new := by
  have hr := removedNodePatches_survivor old new id (sameKind_of_survivor old new id before after ho hn hk)
  have hu : Patch.remove id ∉ new.nodes.toList.flatMap (fun (key, node) => nodePatches old key node) := by
    simp only [List.mem_flatMap]
    rintro ⟨⟨key, node⟩, _, hp⟩
    exact remove_not_nodePatches old key id node hp
  constructor
  · by_cases he : sceneObservation old = sceneObservation new <;>
      by_cases hs : sceneStructure old = sceneStructure new <;>
        simp [diffScene, he, hs, hr, hu, remove_not_children]
  · intro kind
    have hc : Patch.create id kind ∉ new.nodes.toList.flatMap (fun (key, node) => nodePatches old key node) := by
      intro hm
      obtain ⟨⟨key, node⟩, hm, hp⟩ := List.mem_flatMap.mp hm
      by_cases hi : key = id
      · subst key
        have hn' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm
        have he : node = after := by simpa [hn] using hn'.symm
        subst node
        simp [nodePatches, ho, hk] at hp
      · exact create_not_nodePatches_of_other old key id node kind hi hp
    by_cases he : sceneObservation old = sceneObservation new <;>
      by_cases hs : sceneStructure old = sceneStructure new <;>
        simp [diffScene, he, hs, hc, create_not_removedNodePatches, create_not_children]

theorem sceneStructure_lookup (old new : Scene) (h : sceneStructure old = sceneStructure new)
    (id : Nat) : (old.nodes[id]?).map (fun node => (node.kind, node.children)) =
      (new.nodes[id]?).map (fun node => (node.kind, node.children)) := by
  let project := fun (_ : Nat) (node : Node) => (node.kind, node.children)
  have hm : old.nodes.map project = new.nodes.map project := by
    apply Std.ExtTreeMap.toList_inj.mp
    simpa only [Std.ExtTreeMap.toList_map, sceneStructure, project] using congrArg Prod.snd h
  have hl := congrArg (fun (nodes : Std.ExtTreeMap Nat (NodeKind × List Nat)) => nodes[id]?) hm
  simpa only [Std.ExtTreeMap.getElem?_map] using hl

theorem node_of_sameStructure (old new : Scene) (h : sceneStructure old = sceneStructure new)
    (id : Nat) (before : Node) (ho : old.nodes[id]? = some before) :
    ∃ after, new.nodes[id]? = some after ∧ before.kind = after.kind := by
  have hl := sceneStructure_lookup old new h id
  rw [ho] at hl
  cases hn : new.nodes[id]? with
  | none => simp [hn] at hl
  | some after =>
    refine ⟨after, rfl, ?_⟩
    have he : (before.kind, before.children) = (after.kind, after.children) := by
      simpa [hn] using hl
    exact congrArg Prod.fst he

theorem removedNodePatches_of_sameStructure (old new : Scene)
    (h : sceneStructure old = sceneStructure new) : removedNodePatches old new = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  rintro ⟨id, before⟩ hm
  have ho := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm
  obtain ⟨after, hn, hk⟩ := node_of_sameStructure old new h id before ho
  simp [sameKind_of_survivor old new id before after ho hn hk]

theorem diffScene_propertyOnly (old new : Scene) (h : sceneStructure old = sceneStructure new)
    (patch : Patch) (hm : patch ∈ diffScene old new) : ∃ id value, patch = .property id value := by
  by_cases he : sceneObservation old = sceneObservation new
  · simp [diffScene, he] at hm
  · simp only [diffScene, equal_true, he, ite_false, h, ite_true,
      removedNodePatches_of_sameStructure old new h, List.nil_append, List.append_nil] at hm
    obtain ⟨⟨id, after⟩, hn, hp⟩ := List.mem_flatMap.mp hm
    have hn' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hn
    obtain ⟨before, ho, hk⟩ := node_of_sameStructure new old h.symm id after hn'
    simp only [nodePatches, ho, hk.symm, ite_true] at hp
    obtain ⟨value, _, hv⟩ := List.mem_map.mp hp
    exact ⟨id, value, hv.symm⟩

end Kotlean.View
