import Kotlean.Ui.Facts

namespace Kotlean.Ui.Numbering

def references (nodes : List (Nat × View.Node)) : List Nat :=
  nodes.flatMap (fun entry => entry.2.children)

def GoodNodes (nodes : List (Nat × View.Node)) : Prop :=
  ∀ entry ∈ nodes, View.Laws.capacity entry.2.kind entry.2.children.length ∧
    ∀ child ∈ entry.2.children, entry.1 < child ∧ child ∈ nodes.map Prod.fst

structure ChunkFacts {Msg : Type} (start : Nat) (chunk : Chunk Msg) : Prop where
  next : chunk.next = start + chunk.nodes.length
  keys : chunk.nodes.map Prod.fst = List.range' start chunk.nodes.length
  root_rule : chunk.root = if chunk.nodes.length = 0 then none else some start
  root_subset : chunk.root.toList.Sublist (chunk.nodes.map Prod.fst)
  balance : ∀ id, chunk.root.toList.count id + (references chunk.nodes).count id = (chunk.nodes.map Prod.fst).count id
  graph : GoodNodes chunk.nodes

structure ForestFacts {Msg : Type} (trees : List (Ui Msg)) (start : Nat) (forest : Forest Msg) : Prop where
  next : forest.next = start + forest.nodes.length
  keys : forest.nodes.map Prod.fst = List.range' start forest.nodes.length
  root_subset : forest.roots.Sublist (forest.nodes.map Prod.fst)
  balance : ∀ id, forest.roots.count id + (references forest.nodes).count id = (forest.nodes.map Prod.fst).count id
  graph : GoodNodes forest.nodes
  arity : forest.roots.length ≤ trees.length

theorem capacity_mono (kind : NodeKind) (large small : Nat) (bound : small ≤ large)
    (validity : View.Laws.capacity kind large) : View.Laws.capacity kind small := by
  cases kind <;> simp_all [View.Laws.capacity] <;> omega

theorem references_append (first second : List (Nat × View.Node)) :
    references (first ++ second) = references first ++ references second :=
  List.flatMap_append

private theorem facts_all {Msg : Type} (properties : Attributes Msg → Properties) :
    (∀ tree start chunk, Laws.Layout properties tree start chunk → ChunkFacts start chunk) ∧
    (∀ trees start forest, Laws.ForestLayout properties trees start forest → ForestFacts trees start forest) := by
  apply layout_mutual properties (fun _ start chunk => ChunkFacts start chunk)
    (fun trees start forest => ForestFacts trees start forest)
  · intro start
    refine ⟨rfl, rfl, rfl, by simp, ?_, ?_⟩
    · intro id; rfl
    · intro entry member; cases member
  · intro tree kind attributes children form start forest rendered facts
    have capacity := capacity_mono kind children.length forest.roots.length facts.arity
      (form_capacity tree kind attributes children form)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have next := facts.next
      change forest.next = start + (forest.nodes.length + 1)
      omega
    · simpa only [List.map_cons, List.length_cons, List.range'_succ] using
        congrArg (List.cons start) facts.keys
    · simp
    · simp
    · intro id
      have balance := facts.balance id
      change [start].count id + (forest.roots ++ references forest.nodes).count id =
        ([start] ++ forest.nodes.map Prod.fst).count id
      simp only [List.count_append]
      omega
    · intro entry member
      rcases List.mem_cons.mp member with equal | member
      · subst entry
        refine ⟨capacity, ?_⟩
        intro child childMember
        have key := facts.root_subset.subset childMember
        have ranged := key
        rw [facts.keys] at ranged
        have bound := (List.mem_range'_1.mp ranged).1
        refine ⟨by omega, ?_⟩
        exact List.mem_cons_of_mem start key
      · obtain ⟨validity, children⟩ := facts.graph entry member
        refine ⟨validity, ?_⟩
        intro child childMember
        have edge := children child childMember
        exact ⟨edge.1, List.mem_cons_of_mem start edge.2⟩
  · intro start
    refine ⟨rfl, rfl, by simp, ?_, ?_, by simp⟩
    · intro id; rfl
    · intro entry member; cases member
  · intro tree rest start first following rendered continued firstFacts followingFacts
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have firstNext := firstFacts.next
      have followingNext := followingFacts.next
      change following.next = start + (first.nodes ++ following.nodes).length
      rw [List.length_append]
      omega
    · change (first.nodes ++ following.nodes).map Prod.fst =
        List.range' start (first.nodes ++ following.nodes).length
      simp only [List.map_append, List.length_append]
      rw [firstFacts.keys, followingFacts.keys, firstFacts.next]
      exact List.range'_append_1
    · simpa only [List.map_append] using firstFacts.root_subset.append followingFacts.root_subset
    · intro id
      have firstBalance := firstFacts.balance id
      have followingBalance := followingFacts.balance id
      change (first.root.toList ++ following.roots).count id +
        (references (first.nodes ++ following.nodes)).count id =
          ((first.nodes ++ following.nodes).map Prod.fst).count id
      simp only [references_append, List.map_append, List.count_append]
      omega
    · intro entry member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨validity, children⟩ := firstFacts.graph entry member
        refine ⟨validity, ?_⟩
        intro child childMember
        have edge := children child childMember
        exact ⟨edge.1, by simpa only [List.map_append] using List.mem_append_left _ edge.2⟩
      · obtain ⟨validity, children⟩ := followingFacts.graph entry member
        refine ⟨validity, ?_⟩
        intro child childMember
        have edge := children child childMember
        exact ⟨edge.1, by simpa only [List.map_append] using List.mem_append_right _ edge.2⟩
    · have one : first.root.toList.length ≤ 1 := by cases first.root <;> simp
      have restBound := followingFacts.arity
      change (first.root.toList ++ following.roots).length ≤ (tree :: rest).length
      simp only [List.length_append, List.length_cons]
      omega

theorem layout_facts {Msg : Type} (properties : Attributes Msg → Properties)
    (tree : Ui Msg) (start : Nat) (chunk : Chunk Msg) (layout : Laws.Layout properties tree start chunk) :
    ChunkFacts start chunk :=
  (facts_all properties).1 tree start chunk layout

theorem forest_facts {Msg : Type} (properties : Attributes Msg → Properties)
    (trees : List (Ui Msg)) (start : Nat) (forest : Forest Msg)
    (layout : Laws.ForestLayout properties trees start forest) : ForestFacts trees start forest :=
  (facts_all properties).2 trees start forest layout

end Kotlean.Ui.Numbering
