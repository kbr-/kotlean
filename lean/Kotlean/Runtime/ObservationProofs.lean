import Kotlean.Runtime.Observation
import Kotlean.View.Diff

namespace Kotlean.View.Canonical

theorem preorder_map (nodes : Std.ExtTreeMap Nat Node) (transform : Nat → Node → Node)
    (children : ∀ id node, (transform id node).children = node.children) (fuel id : Nat) :
    preorder (nodes.map transform) fuel id = preorder nodes fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    simp only [preorder, Std.ExtTreeMap.getElem?_map]
    cases nodes[id]? with
    | none => rfl
    | some node =>
      simp only [Option.map_some, children]
      rw [funext ih]

theorem valid_map (scene : Scene) (transform : Nat → Node → Node)
    (kind : ∀ id node, (transform id node).kind = node.kind)
    (children : ∀ id node, (transform id node).children = node.children)
    (validity : valid scene) : valid { scene with nodes := scene.nodes.map transform } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.ExtTreeMap.toList_map, List.length_map, List.map_map, Function.comp_def] using validity.1
  · simpa only [Std.ExtTreeMap.toList_map, List.length_map] using validity.2.1
  · intro entry member
    rw [Std.ExtTreeMap.toList_map] at member
    obtain ⟨⟨id, node⟩, oldMember, rfl⟩ := List.mem_map.mp member
    have original := validity.2.2.1 (id, node) oldMember
    constructor
    · simpa only [kind, children] using original.1
    · intro child childMember
      have edge := original.2 child (by simpa only [children] using childMember)
      exact ⟨edge.1, by simpa using edge.2⟩
  · simpa only [Std.ExtTreeMap.toList_map, List.length_map, List.flatMap_map, Function.comp_def,
      children] using validity.2.2.2.1
  · simpa only [Std.ExtTreeMap.toList_map, List.length_map] using
      (preorder_map scene.nodes transform children scene.nodes.toList.length 0).trans validity.2.2.2.2

end Kotlean.View.Canonical

namespace Kotlean.View

private theorem text_not_properties (old new : Properties) (same : old.text = new.text) (value : String) :
    Property.text value ∉ diffProperties old new := by
  intro member
  have relation := (mem_diffProperties old new (.text value)).mp member
  have valueSame : value = new.text := congrArg Properties.text relation.2
  have unchanged : applyProperty (.text value) old = old := by
    rw [valueSame.trans same.symm]
    rfl
  exact relation.1 unchanged

private theorem property_not_other (old : Scene) (key id : Nat) (node : Node) (property : Property)
    (different : key ≠ id) : Patch.property id property ∉ nodePatches old key node := by
  cases found : old.nodes[key]? with
  | none => simp [nodePatches, found, createNodePatches, different]
  | some before =>
    by_cases same : before.kind = node.kind <;>
      simp [nodePatches, found, same, createNodePatches, different]

private theorem property_not_removed (old new : Scene) (id : Nat) (property : Property) :
    Patch.property id property ∉ removedNodePatches old new := by
  intro member
  obtain ⟨⟨key, node⟩, _, selected⟩ := List.mem_filterMap.mp member
  split at selected <;> simp at selected

private theorem property_not_children (entries : List (Nat × Node)) (id : Nat) (property : Property) :
    Patch.property id property ∉ childPatches entries := by
  simp [childPatches, List.mem_flatMap, List.mem_mapIdx]

theorem diffScene_text_unchanged (old new : Scene) (id : Nat) (before after : Node)
    (oldLookup : old.nodes[id]? = some before) (newLookup : new.nodes[id]? = some after)
    (sameKind : before.kind = after.kind) (sameText : before.properties.text = after.properties.text)
    (value : String) : Patch.property id (.text value) ∉ diffScene old new := by
  have nodes : Patch.property id (.text value) ∉
      new.nodes.toList.flatMap (fun (key, node) => nodePatches old key node) := by
    intro member
    obtain ⟨⟨key, node⟩, nodeMember, patchMember⟩ := List.mem_flatMap.mp member
    by_cases sameId : key = id
    · subst key
      have lookup := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp nodeMember
      have equalNode : node = after := by simpa [newLookup] using lookup.symm
      subst node
      simp only [nodePatches, oldLookup, sameKind, ite_true] at patchMember
      obtain ⟨property, propertyMember, equalPatch⟩ := List.mem_map.mp patchMember
      have equalProperty : property = .text value := by simpa using equalPatch
      subst property
      exact text_not_properties before.properties after.properties sameText value propertyMember
    · exact property_not_other old key id node (.text value) sameId patchMember
  by_cases equalScene : sceneObservation old = sceneObservation new <;>
    by_cases equalStructure : sceneStructure old = sceneStructure new <;>
      simp [diffScene, equalScene, equalStructure, nodes, property_not_removed, property_not_children]

end Kotlean.View

namespace Kotlean.Runtime

theorem edited_valid (scene : View.Scene) (id : Nat) (text : String)
    (validity : View.Canonical.valid scene) : View.Canonical.valid (edited scene id text) := by
  apply View.Canonical.valid_map
  · intro key node
    split <;> rfl
  · intro key node
    split <;> rfl
  · exact validity

theorem observed_valid (scene : View.Scene) (revision : Nat) (event : Event)
    (validity : View.Canonical.valid scene) : View.Canonical.valid (observed scene revision event) := by
  cases event with
  | node received id input =>
    cases input <;> simp only [observed]
    all_goals try exact validity
    split
    · exact edited_valid scene id _ validity
    · exact validity
  | answer | subscription | lifecycle | save => exact validity

end Kotlean.Runtime
