module
public import Kotlean.View.Model
public import Kotlean.View.Properties

@[expose] public section

namespace Kotlean.View

def childCapacity (kind : NodeKind) (count : Nat) : Bool :=
  match kind with
  | .column | .row => true
  | .scroll => count ≤ 1
  | .text | .button | .input | .canvas => count == 0

def detachChild (child : Nat) (node : Node) : Node :=
  { node with children := node.children.filter (· ≠ child) }

def insertChild (index child : Nat) (children : List Nat) : List Nat :=
  children.take index ++ child :: children.drop index

def applyPatch (patch : Patch) (state : Scene) : Option Scene :=
  match patch with
  | .create id kind =>
    if state.nodes[id]?.isSome then none
    else some { state with nodes := state.nodes.insert id { kind := kind } }
  | .property id property => do
    let node ← state.nodes[id]?
    let updated := { node with properties := applyProperty property node.properties }
    return { state with nodes := state.nodes.insert id updated }
  | .remove id =>
    if state.nodes[id]?.isSome then
      some { nodes := (state.nodes.erase id).map (fun _ => detachChild id)
             root := if state.root = some id then none else state.root }
    else none
  | .insert parent index child => do
    let node ← state.nodes[parent]?
    let _ ← state.nodes[child]?
    let remaining := (detachChild child node).children
    if parent < child && index ≤ remaining.length && childCapacity node.kind (remaining.length + 1) then
      let updated := { node with children := insertChild index child remaining }
      let nodes := (state.nodes.map (fun _ => detachChild child)).insert parent updated
      return { state with nodes := nodes }
    else none
  | .root root =>
    if root.all (fun id => state.nodes[id]?.isSome) then some { state with root := root }
    else none

def applyPatches (patches : List Patch) (state : Scene) : Option Scene :=
  patches.foldlM (fun state patch => applyPatch patch state) state

theorem lookup_insert (nodes : Std.ExtTreeMap Nat Node) (id key : Nat) (node : Node) :
    (nodes.insert id node)[key]? = if key = id then some node else nodes[key]? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_eq_iff_eq]
  by_cases h : id = key
  · subst key; simp
  · simp [h, Ne.symm h]

theorem lookup_detach (nodes : Std.ExtTreeMap Nat Node) (id key : Nat) :
    (nodes.map (fun _ => detachChild id))[key]? = (nodes[key]?).map (detachChild id) := by
  simp

theorem lookup_remove (nodes : Std.ExtTreeMap Nat Node) (id key : Nat) :
    ((nodes.erase id).map (fun _ => detachChild id))[key]? =
      if key = id then none else (nodes[key]?).map (detachChild id) := by
  simp only [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_erase]
  simp only [Std.compare_eq_eq_iff_eq]
  by_cases h : id = key
  · subst key; simp
  · simp [h, Ne.symm h]

theorem applyPatches_nil (state : Scene) : applyPatches [] state = some state := rfl

theorem applyPatches_cons (patch : Patch) (patches : List Patch) (state : Scene) :
    applyPatches (patch :: patches) state =
      (applyPatch patch state).bind (applyPatches patches) := by
  rfl

theorem applyPatches_append (first second : List Patch) (state : Scene) :
    applyPatches (first ++ second) state =
      (applyPatches first state).bind (applyPatches second) := by
  induction first generalizing state with
  | nil => rfl
  | cons patch rest ih =>
    simp only [List.cons_append, applyPatches_cons]
    cases applyPatch patch state <;> simp [ih]

end Kotlean.View
