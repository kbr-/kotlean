import Kotlean.Ui.Types

namespace Kotlean.Ui.Registry

theorem ofList_toList {Value : Type} (entries : List (Nat × Value))
    (sorted : entries.Pairwise (fun a b => a.1 < b.1)) :
    (Std.ExtTreeMap.ofList entries).toList = entries := by
  classical
  let table := Std.ExtTreeMap.ofList entries
  have distinct : entries.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := by
    apply sorted.imp
    intro a b less equal
    have same : a.1 = b.1 := Std.compare_eq_eq_iff_eq.mp equal
    omega
  have ordered : table.toList.Pairwise (fun a b => a.1 < b.1) := by
    simpa only [Nat.compare_eq_lt] using table.ordered_keys_toList
  have noDuplicates : entries.Nodup := by
    apply sorted.imp
    intro a b less equal
    have same := congrArg Prod.fst equal
    omega
  have tableNoDuplicates : table.toList.Nodup := by
    apply ordered.imp
    intro a b less equal
    have same := congrArg Prod.fst equal
    omega
  have members : ∀ entry, entry ∈ table.toList ↔ entry ∈ entries := by
    intro entry
    obtain ⟨key, value⟩ := entry
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    constructor
    · intro lookup
      have present : key ∈ entries.map Prod.fst := by
        have found := congrArg Option.isSome lookup
        simpa [table] using found
      obtain ⟨⟨sourceKey, sourceValue⟩, member, equal⟩ := List.mem_map.mp present
      dsimp at equal
      subst sourceKey
      have source : table[key]? = some sourceValue :=
        Std.ExtTreeMap.getElem?_ofList_of_mem (by simp) distinct member
      have same : sourceValue = value := Option.some.inj (source.symm.trans lookup)
      subst sourceValue
      exact member
    · intro member
      exact Std.ExtTreeMap.getElem?_ofList_of_mem (by simp) distinct member
  have permutation := (List.perm_ext_iff_of_nodup tableNoDuplicates noDuplicates).mpr members
  exact List.Perm.eq_of_pairwise (fun a b _ _ less reverse => by omega) ordered sorted permutation

end Kotlean.Ui.Registry
