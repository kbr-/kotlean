import Kotlean.View.Diff

namespace Kotlean.View

theorem insert_present (state : Scene) (id : Nat) (node : Node)
    (h : state.nodes[id]? = some node) : state.nodes.insert id node = state.nodes := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  rw [lookup_insert]
  split
  · next hk => subst key; exact h.symm
  · rfl

theorem propertyPatches_apply (changes : List Property) (state : Scene) (id : Nat) (node : Node)
    (h : state.nodes[id]? = some node) :
    applyPatches (changes.map (Patch.property id)) state =
      some { state with nodes := state.nodes.insert id (
        { node with properties := applyProperties node.properties changes }) } := by
  induction changes generalizing state node with
  | nil =>
    simp [applyProperties, applyPatches, insert_present state id node h]
  | cons property rest ih =>
    rw [List.map_cons, applyPatches_cons]
    simp only [applyPatch, h, bind, Option.bind, pure]
    rw [ih _ { node with properties := applyProperty property node.properties }
      (by simp)]
    congr 1
    congr 1
    apply Std.ExtTreeMap.ext_getElem?
    intro key
    by_cases hk : key = id
    · subst key; simp [applyProperties]
    · simp [lookup_insert, hk]

theorem nodePropertyDiff_apply (state : Scene) (id : Nat) (node : Node) (new : Properties)
    (h : state.nodes[id]? = some node) :
    applyPatches ((diffProperties node.properties new).map (Patch.property id)) state =
      some { state with nodes := state.nodes.insert id { node with properties := new } } := by
  rw [propertyPatches_apply _ _ _ _ h, apply_diffProperties]

theorem apply_allProperties (old new : Properties) :
    applyProperties old (allProperties new) = new := by
  cases old
  cases new
  rfl

theorem createNodePatches_apply (state : Scene) (id : Nat) (node : Node)
    (h : state.nodes[id]? = none) :
    applyPatches (createNodePatches id node) state =
      some { state with nodes := state.nodes.insert id (
        { kind := node.kind, properties := node.properties } : Node) } := by
  rw [createNodePatches, applyPatches_cons]
  simp only [applyPatch, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
  rw [propertyPatches_apply _ _ _ ({ kind := node.kind } : Node) (by simp), apply_allProperties]
  congr 1
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  by_cases hk : key = id <;> simp [lookup_insert, hk]

theorem retainedNodePatches_apply (old state : Scene) (id : Nat) (before current target : Node)
    (ho : old.nodes[id]? = some before) (hs : state.nodes[id]? = some current)
    (hk : before.kind = target.kind) (hp : current.properties = before.properties) :
    applyPatches (nodePatches old id target) state =
      some { state with nodes := state.nodes.insert id (
        { current with properties := target.properties }) } := by
  simp only [nodePatches, ho, hk, ↓reduceIte]
  rw [← hp]
  exact nodePropertyDiff_apply state id current target.properties hs


def withoutChildren (ids : List Nat) (node : Node) : Node :=
  { node with children := node.children.filter (fun child => decide (child ∉ ids)) }

theorem withoutChildren_cons (id : Nat) (ids : List Nat) (node : Node) :
    withoutChildren ids (detachChild id node) = withoutChildren (id :: ids) node := by
  cases node
  simp [withoutChildren, detachChild, List.filter_filter, Bool.and_comm]

theorem removePatches_apply (ids : List Nat) (state : Scene) (distinct : ids.Nodup)
    (present : ∀ id ∈ ids, (state.nodes[id]?).isSome = true) :
    ∃ result,
      applyPatches (ids.map Patch.remove) state = some result ∧
      result.root = state.root.bind (fun id => if id ∈ ids then none else some id) ∧
      ∀ key, result.nodes[key]? =
        if key ∈ ids then none else (state.nodes[key]?).map (withoutChildren ids) := by
  induction ids generalizing state with
  | nil =>
    refine ⟨state, rfl, ?_, ?_⟩
    · cases state.root <;> simp
    · intro key
      cases h : state.nodes[key]? with
      | none => simp
      | some node =>
        have hf : node.children.filter (fun _ => true) = node.children :=
          List.filter_eq_self.mpr (by simp)
        simp [withoutChildren, hf]
  | cons id rest ih =>
    have hd := List.nodup_cons.mp distinct
    have hp := present id (by simp)
    cases hn : state.nodes[id]? with
    | none => simp [hn] at hp
    | some node =>
      let next : Scene :=
        { nodes := (state.nodes.erase id).map (fun _ => detachChild id)
          root := if state.root = some id then none else state.root }
      have hnext : ∀ key ∈ rest, (next.nodes[key]?).isSome = true := by
        intro key hk
        have ne : key ≠ id := by intro he; subst key; exact hd.1 hk
        have hx := present key (by simp [hk])
        simpa [next, ne, Ne.symm ne] using hx
      obtain ⟨result, ha, hr, hv⟩ := ih next hd.2 hnext
      refine ⟨result, ?_, ?_, ?_⟩
      · simpa [List.map_cons, applyPatches_cons, applyPatch, hn, next] using ha
      · rw [hr]
        cases hroot : state.root with
        | none => simp [next, hroot]
        | some root =>
          by_cases he : root = id <;> simp [next, hroot, he]
      · intro key
        rw [hv]
        by_cases he : key = id
        · subst key; simp [next]
        · by_cases hm : key ∈ rest
          · simp [hm]
          · simp only [hm, ↓reduceIte, List.mem_cons, he, false_or]
            have hl : next.nodes[key]? = (state.nodes[key]?).map (detachChild id) := by
              simpa only [he, ↓reduceIte] using lookup_remove state.nodes id key
            rw [hl, Option.map_map]
            congr 1
            funext value
            exact withoutChildren_cons id rest value


def nodeReady (old state : Scene) (id : Nat) (target : Node) : Prop :=
  match old.nodes[id]? with
  | none => state.nodes[id]? = none
  | some before =>
    if before.kind = target.kind then
      ∃ current, state.nodes[id]? = some current ∧ current.kind = target.kind ∧
        current.properties = before.properties
    else state.nodes[id]? = none

def preparedNode (state : Scene) (id : Nat) (target : Node) : Node :=
  { target with children := ((state.nodes[id]?).map Node.children).getD [] }

theorem nodePatches_ready_apply (old state : Scene) (id : Nat) (target : Node)
    (ready : nodeReady old state id target) :
    applyPatches (nodePatches old id target) state =
      some { state with nodes := state.nodes.insert id (preparedNode state id target) } := by
  cases ho : old.nodes[id]? with
  | none =>
    have hs : state.nodes[id]? = none := by simpa [nodeReady, ho] using ready
    simp only [nodePatches, ho]
    rw [createNodePatches_apply state id target hs]
    simp [preparedNode, hs]
  | some before =>
    by_cases hk : before.kind = target.kind
    · obtain ⟨current, hs, hc, hp⟩ := by simpa [nodeReady, ho, hk] using ready
      rw [retainedNodePatches_apply old state id before current target ho hs hk hp]
      simp [preparedNode, hs, hc]
    · have hs : state.nodes[id]? = none := by simpa [nodeReady, ho, hk] using ready
      simp only [nodePatches, ho, hk, ↓reduceIte]
      rw [createNodePatches_apply state id target hs]
      simp [preparedNode, hs]


def prepareRecords (entries : List (Nat × Node)) (state : Scene) : Scene :=
  entries.foldl (fun current (id, target) =>
    { current with nodes := current.nodes.insert id (preparedNode current id target) }) state

theorem nodePhase_apply (entries : List (Nat × Node)) (old state : Scene)
    (distinct : (entries.map Prod.fst).Nodup)
    (ready : ∀ entry ∈ entries, nodeReady old state entry.1 entry.2) :
    applyPatches (entries.flatMap (fun (id, target) => nodePatches old id target)) state =
      some (prepareRecords entries state) := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨id, target⟩ := entry
    have hd := List.nodup_cons.mp distinct
    have hf := ready (id, target) (by simp)
    rw [List.flatMap_cons, applyPatches_append, nodePatches_ready_apply old state id target hf]
    simp only [Option.bind_some]
    let next : Scene := { state with nodes := state.nodes.insert id (preparedNode state id target) }
    change applyPatches (rest.flatMap (fun (key, node) => nodePatches old key node)) next =
      some (prepareRecords rest next)
    apply ih next hd.2
    intro entry hm
    have hn : entry.1 ≠ id := by
      intro he
      exact hd.1 (List.mem_map.mpr ⟨entry, hm, he⟩)
    have hr := ready entry (by simp [hm])
    simpa [nodeReady, next, lookup_insert, hn] using hr


def removedIds (old new : Scene) : List Nat :=
  old.nodes.keys.filter (fun id => !sameKind old new id)

theorem removedIds_map (old new : Scene) :
    (removedIds old new).map Patch.remove = removedNodePatches old new := by
  unfold removedIds removedNodePatches
  rw [← Std.ExtTreeMap.map_fst_toList_eq_keys]
  generalize old.nodes.toList = entries
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨id, node⟩ := entry
    cases hs : sameKind old new id <;> simp [hs, ih]

theorem mem_removedIds (old new : Scene) (id : Nat) :
    id ∈ removedIds old new ↔ (old.nodes[id]?).isSome = true ∧ sameKind old new id = false := by
  simp [removedIds]

theorem removedPhase_ready (old new : Scene) :
    ∃ state, applyPatches (removedNodePatches old new) old = some state ∧
      (∀ id target, new.nodes[id]? = some target → nodeReady old state id target) ∧
      state.root = old.root.bind (fun id => if id ∈ removedIds old new then none else some id) ∧
      ∀ key, state.nodes[key]? = if key ∈ removedIds old new then none
        else (old.nodes[key]?).map (withoutChildren (removedIds old new)) := by
  have hd : (removedIds old new).Nodup := old.nodes.nodup_keys.filter _
  have hp : ∀ id ∈ removedIds old new, (old.nodes[id]?).isSome = true := by
    intro id hm
    exact ((mem_removedIds old new id).mp hm).1
  obtain ⟨state, ha, hr, hv⟩ := removePatches_apply (removedIds old new) old hd hp
  refine ⟨state, ?_, ?_, hr, hv⟩
  · simpa only [removedIds_map] using ha
  · intro id target hn
    cases ho : old.nodes[id]? with
    | none =>
      have hs : state.nodes[id]? = none := by simpa [ho] using hv id
      simpa [nodeReady, ho] using hs
    | some before =>
      by_cases hk : before.kind = target.kind
      · have hm : id ∉ removedIds old new := by
          simp [mem_removedIds, sameKind, ho, hn, hk]
        have hs : state.nodes[id]? = some (withoutChildren (removedIds old new) before) := by
          simpa [hm, ho] using hv id
        simp only [nodeReady, ho, hk, ↓reduceIte]
        exact ⟨_, hs, hk, rfl⟩
      · have hm : id ∈ removedIds old new := by
          simp [mem_removedIds, sameKind, ho, hn, hk]
        have hs : state.nodes[id]? = none := by simpa [hm] using hv id
        simpa [nodeReady, ho, hk] using hs

theorem removal_and_preparation_succeed (old new : Scene) :
    ∃ result, applyPatches (removedNodePatches old new ++
      new.nodes.toList.flatMap (fun (id, target) => nodePatches old id target)) old = some result := by
  obtain ⟨state, hr, ready, _⟩ := removedPhase_ready old new
  refine ⟨prepareRecords new.nodes.toList state, ?_⟩
  rw [applyPatches_append, hr, Option.bind_some]
  apply nodePhase_apply
  · simpa using new.nodes.nodup_keys
  · intro entry he
    exact ready entry.1 entry.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp he)


theorem prepareRecords_observation (entries : List (Nat × Node)) (state : Scene)
    (distinct : (entries.map Prod.fst).Nodup) :
    (prepareRecords entries state).root = state.root ∧
    (∀ entry ∈ entries, (prepareRecords entries state).nodes[entry.1]? =
      some (preparedNode state entry.1 entry.2)) ∧
    (∀ key, key ∉ entries.map Prod.fst →
      (prepareRecords entries state).nodes[key]? = state.nodes[key]?) := by
  induction entries generalizing state with
  | nil => simp [prepareRecords]
  | cons first rest ih =>
    obtain ⟨id, target⟩ := first
    have hd := List.nodup_cons.mp distinct
    let next : Scene := { state with nodes := state.nodes.insert id (preparedNode state id target) }
    have he : prepareRecords ((id, target) :: rest) state = prepareRecords rest next := rfl
    rw [he]
    obtain ⟨hr, hv, ho⟩ := ih next hd.2
    refine ⟨hr, ?_, ?_⟩
    · intro entry hm
      rcases List.mem_cons.mp hm with he | hm
      · subst entry
        rw [ho id hd.1]
        simp [next]
      · have hn : entry.1 ≠ id := by
          intro he
          exact hd.1 (List.mem_map.mpr ⟨entry, hm, he⟩)
        simpa [preparedNode, next, lookup_insert, hn] using hv entry hm
    · intro key hk
      have hn : key ≠ id := by
        intro he
        subst key
        exact hk (by simp)
      have hm : key ∉ rest.map Prod.fst := by
        intro hm
        exact hk (by simp [hm])
      rw [ho key hm]
      simp [next, lookup_insert, hn]


def remainingNode (old new : Scene) (key : Nat) : Option Node :=
  if key ∈ removedIds old new then none
  else (old.nodes[key]?).map (withoutChildren (removedIds old new))

def preparedScene (old new : Scene) : Scene :=
  { nodes := new.nodes.map (fun id target =>
      { target with children := ((remainingNode old new id).map Node.children).getD [] })
    root := old.root.bind (fun id => if id ∈ removedIds old new then none else some id) }

theorem scene_eq_of_fields (left right : Scene) (hr : left.root = right.root)
    (hn : left.nodes = right.nodes) : left = right := by
  cases left
  cases right
  cases hr
  cases hn
  rfl

theorem preparation_exact (old new : Scene) :
    applyPatches (removedNodePatches old new ++
      new.nodes.toList.flatMap (fun (id, target) => nodePatches old id target)) old =
      some (preparedScene old new) := by
  obtain ⟨state, hr, ready, hroot, hvalues⟩ := removedPhase_ready old new
  have hd : (new.nodes.toList.map Prod.fst).Nodup := by simpa using new.nodes.nodup_keys
  rw [applyPatches_append, hr, Option.bind_some, nodePhase_apply new.nodes.toList old state hd]
  · apply congrArg some
    obtain ⟨proot, pvalues, poutside⟩ := prepareRecords_observation new.nodes.toList state hd
    apply scene_eq_of_fields
    · exact proot.trans hroot
    · apply Std.ExtTreeMap.ext_getElem?
      intro key
      cases hn : new.nodes[key]? with
      | some target =>
        have hm : (key, target) ∈ new.nodes.toList :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hn
        rw [pvalues (key, target) hm]
        simp [preparedScene, hn, preparedNode, hvalues, remainingNode]
      | none =>
        have hm : key ∉ new.nodes.toList.map Prod.fst := by
          simp only [Std.ExtTreeMap.map_fst_toList_eq_keys, Std.ExtTreeMap.mem_keys]
          intro hm
          have hx := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm
          simp [hn] at hx
        rw [poutside key hm]
        rw [hvalues]
        simp only [preparedScene, Std.ExtTreeMap.getElem?_map, hn, Option.map_none]
        cases ho : old.nodes[key]? with
        | none => simp
        | some before =>
          have removed : key ∈ removedIds old new := by
            simp [mem_removedIds, sameKind, ho, hn]
          simp [removed]
  · intro entry hm
    exact ready entry.1 entry.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hm)


theorem sameStructure_lookup (old new : Scene) (hs : sceneStructure old = sceneStructure new)
    (key : Nat) :
    (old.nodes[key]?).map (fun node => (node.kind, node.children)) =
      (new.nodes[key]?).map (fun node => (node.kind, node.children)) := by
  have hl := congrArg Prod.snd hs
  have hm : (old.nodes.map (fun _ node => (node.kind, node.children))).toList =
      (new.nodes.map (fun _ node => (node.kind, node.children))).toList := by
    simpa [sceneStructure, Std.ExtTreeMap.toList_map] using hl
  have he := Std.ExtTreeMap.ext_toList (List.Perm.of_eq hm)
  have hx := congrArg (fun (nodes : Std.ExtTreeMap Nat (NodeKind × List Nat)) => nodes[key]?) he
  simpa using hx

theorem sameStructure_removedIds (old new : Scene) (hs : sceneStructure old = sceneStructure new) :
    removedIds old new = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro key hm
  obtain ⟨hp, hk⟩ := (mem_removedIds old new key).mp hm
  have hx := sameStructure_lookup old new hs key
  cases ho : old.nodes[key]? with
  | none => simp [ho] at hp
  | some before =>
    cases hn : new.nodes[key]? with
    | none => simp [ho, hn] at hx
    | some target =>
      have he : before.kind = target.kind := by simpa [ho, hn] using congrArg (Option.map Prod.fst) hx
      simp [sameKind, ho, hn, he] at hk

theorem sameStructure_preparedScene (old new : Scene) (hs : sceneStructure old = sceneStructure new) :
    preparedScene old new = new := by
  have removed := sameStructure_removedIds old new hs
  apply scene_eq_of_fields
  · have hr := congrArg Prod.fst hs
    simpa [preparedScene, removed, sceneStructure] using hr
  · apply Std.ExtTreeMap.ext_getElem?
    intro key
    have hx := sameStructure_lookup old new hs key
    cases hn : new.nodes[key]? with
    | none => simp [preparedScene, hn]
    | some target =>
      cases ho : old.nodes[key]? with
      | none => simp [ho, hn] at hx
      | some before =>
        have hc : before.children = target.children := by
          simpa [ho, hn] using congrArg (Option.map Prod.snd) hx
        have hf : target.children.filter (fun _ => true) = target.children :=
          List.filter_eq_self.mpr (by simp)
        simp [preparedScene, remainingNode, removed, hn, ho, withoutChildren, hf, hc]

theorem sameObservation_eq (old new : Scene) (hs : sceneObservation old = sceneObservation new) :
    old = new := by
  apply scene_eq_of_fields
  · exact congrArg Prod.fst hs
  · exact Std.ExtTreeMap.ext_toList (List.Perm.of_eq (congrArg Prod.snd hs))

theorem diffScene_propertyApplication (old new : Scene)
    (hs : sceneStructure old = sceneStructure new) :
    applyPatches (diffScene old new) old = some new := by
  by_cases he : sceneObservation old = sceneObservation new
  · have ho := sameObservation_eq old new he
    subst new
    simp [diffScene_self, applyPatches_nil]
  · simp only [diffScene, equal_true, he, ↓reduceIte, hs, List.append_nil]
    rw [preparation_exact, sameStructure_preparedScene old new hs]


end Kotlean.View
