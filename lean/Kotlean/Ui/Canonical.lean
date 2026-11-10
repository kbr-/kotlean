import Kotlean.Ui.Numbering
import Kotlean.Ui.Registry
import Kotlean.View.Correctness

namespace Kotlean.Ui

open Numbering

private theorem preorder_all {Msg : Type} (properties : Attributes Msg → Properties) :
    (∀ tree start chunk, Laws.Layout properties tree start chunk →
      ∀ (table : Std.ExtTreeMap Nat View.Node compare) fuel,
        (∀ entry ∈ chunk.nodes, table[entry.1]? = some entry.2) → chunk.nodes.length ≤ fuel →
        chunk.root.toList.flatMap (View.Canonical.preorder table fuel) = chunk.nodes.map Prod.fst) ∧
    (∀ trees start forest, Laws.ForestLayout properties trees start forest →
      ∀ (table : Std.ExtTreeMap Nat View.Node compare) fuel,
        (∀ entry ∈ forest.nodes, table[entry.1]? = some entry.2) → forest.nodes.length ≤ fuel →
        forest.roots.flatMap (View.Canonical.preorder table fuel) = forest.nodes.map Prod.fst) := by
  apply layout_mutual properties
    (fun _ _ chunk => ∀ (table : Std.ExtTreeMap Nat View.Node compare) fuel,
      (∀ entry ∈ chunk.nodes, table[entry.1]? = some entry.2) → chunk.nodes.length ≤ fuel →
      chunk.root.toList.flatMap (View.Canonical.preorder table fuel) = chunk.nodes.map Prod.fst)
    (fun _ _ forest => ∀ (table : Std.ExtTreeMap Nat View.Node compare) fuel,
      (∀ entry ∈ forest.nodes, table[entry.1]? = some entry.2) → forest.nodes.length ≤ fuel →
      forest.roots.flatMap (View.Canonical.preorder table fuel) = forest.nodes.map Prod.fst)
  · intro start table fuel members bound; rfl
  · intro tree kind attributes children form start forest rendered subtree table fuel members bound
    have top := members (start, { kind := kind, properties := properties attributes, children := forest.roots })
      (by simp)
    change forest.nodes.length + 1 ≤ fuel at bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      have rest := subtree table fuel
        (by intro entry member; exact members entry (by simp [member])) (by omega)
      change View.Canonical.preorder table (fuel + 1) start ++ [] = start :: forest.nodes.map Prod.fst
      simpa only [View.Canonical.preorder, top, List.append_nil] using congrArg (List.cons start) rest
  · intro start table fuel members bound; rfl
  · intro tree rest start first following rendered continued firstOrder followingOrder table fuel members bound
    have total : first.nodes.length + following.nodes.length ≤ fuel := by
      simpa only [List.length_append] using bound
    have firstVisits := firstOrder table fuel
      (by intro entry member; exact members entry (List.mem_append_left _ member)) (by omega)
    have followingVisits := followingOrder table fuel
      (by intro entry member; exact members entry (List.mem_append_right _ member)) (by omega)
    change (first.root.toList ++ following.roots).flatMap (View.Canonical.preorder table fuel) =
      (first.nodes ++ following.nodes).map Prod.fst
    rw [List.flatMap_append, firstVisits, followingVisits, List.map_append]

theorem layout_preorder {Msg : Type} (properties : Attributes Msg → Properties)
    (tree : Ui Msg) (start : Nat) (chunk : Chunk Msg) (layout : Laws.Layout properties tree start chunk)
    (table : Std.ExtTreeMap Nat View.Node compare) (fuel : Nat)
    (members : ∀ entry ∈ chunk.nodes, table[entry.1]? = some entry.2) (bound : chunk.nodes.length ≤ fuel) :
    chunk.root.toList.flatMap (View.Canonical.preorder table fuel) = chunk.nodes.map Prod.fst :=
  (preorder_all properties).1 tree start chunk layout table fuel members bound

theorem layout_canonical {Msg : Type} (properties : Attributes Msg → Properties)
    (tree : Ui Msg) (chunk : Chunk Msg) (layout : Laws.Layout properties tree 0 chunk) :
    View.Canonical.valid { nodes := Std.ExtTreeMap.ofList chunk.nodes, root := chunk.root } := by
  have facts := layout_facts properties tree 0 chunk layout
  have keysSorted : (chunk.nodes.map Prod.fst).Pairwise (· < ·) := by
    rw [facts.keys]
    exact List.pairwise_lt_range'
  have sorted : chunk.nodes.Pairwise (fun a b => a.1 < b.1) := by
    simpa only [List.pairwise_map] using keysSorted
  let table := Std.ExtTreeMap.ofList chunk.nodes
  have entries : table.toList = chunk.nodes := Registry.ofList_toList chunk.nodes sorted
  have keys : chunk.nodes.map Prod.fst = List.range chunk.nodes.length := by
    simpa only [← List.range_eq_range'] using facts.keys
  have unique : (chunk.nodes.map Prod.fst).Nodup := by
    apply keysSorted.imp
    intro a b less equal
    omega
  have members : ∀ entry ∈ chunk.nodes, table[entry.1]? = some entry.2 := by
    intro entry member
    apply Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp
    rw [entries]
    exact member
  change View.Canonical.valid { nodes := table, root := chunk.root }
  unfold View.Canonical.valid
  dsimp only
  rw [entries]
  refine ⟨keys, facts.root_rule, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨capacity, children⟩ := facts.graph entry member
    refine ⟨capacity, ?_⟩
    intro child childMember
    have edge := children child childMember
    refine ⟨edge.1, ?_⟩
    have present : child ∈ table := by simpa [table] using edge.2
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mp present
  · intro child member
    have bounds := member
    simp only [List.range_eq_range', List.drop_range', List.mem_range'_1] at bounds
    have positive : child ≠ 0 := by omega
    have inside : child < chunk.nodes.length := by omega
    have nonempty : chunk.nodes.length ≠ 0 := by omega
    have keyMember : child ∈ chunk.nodes.map Prod.fst := by rw [keys]; exact List.mem_range.mpr inside
    have count := List.nodup_iff_count_of_mem.mp unique child keyMember
    have root : chunk.root = some 0 := by simpa only [nonempty, ↓reduceIte] using facts.root_rule
    have balance := facts.balance child
    simpa [references, root, positive, Ne.symm positive, count] using balance
  · by_cases empty : chunk.nodes.length = 0
    · simp [empty, View.Canonical.preorder]
    · have root : chunk.root = some 0 := by simpa only [empty, ↓reduceIte] using facts.root_rule
      have order := layout_preorder properties tree 0 chunk layout table chunk.nodes.length members (by omega)
      have visits : View.Canonical.preorder table chunk.nodes.length 0 = chunk.nodes.map Prod.fst := by
        simpa only [root, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil] using order
      rw [visits, keys]

theorem compile_canonical {Msg : Type} : Laws.canonicalContract (@compile Msg) := by
  intro tree
  exact layout_canonical (@Attributes.renderProperties Msg) tree (renderAt tree 0) (renderAt_layout tree 0)

theorem compile_diff_correct {Old New : Type} (old : Ui Old) (new : Ui New) :
    View.applyPatches (View.diffScene (compile old).scene (compile new).scene) (compile old).scene =
      some (compile new).scene :=
  View.diffScene_correct _ _ (compile_canonical old) (compile_canonical new)

theorem no_patches_same_shape {Left Right : Type} (left : Ui Left) (right : Ui Right)
    (shape : Laws.SameShape (@Attributes.renderProperties Left) (@Attributes.renderProperties Right) left right) :
    View.diffScene (compile left).scene (compile right).scene = [] := by
  rw [compile_same_shape left right shape]
  exact View.diffScene_self _

end Kotlean.Ui
