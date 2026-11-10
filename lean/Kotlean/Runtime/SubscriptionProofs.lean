module
public import Kotlean.Runtime.Subscriptions

@[expose] public section

namespace Kotlean.Runtime.Subscriptions

@[simp] theorem fresh_sources (next : Nat) (sources : List Source) :
    (fresh next sources).map Subscription.source = sources := by
  simp [fresh, List.map_map, Function.comp_def]

@[simp] theorem fresh_ids (next : Nat) (sources : List Source) :
    (fresh next sources).map Subscription.id = List.range' next sources.length := by
  simp [fresh, List.map_map, Function.comp_def]

theorem fresh_bounds (next : Nat) (sources : List Source) (binding : Subscription)
    (member : binding ∈ fresh next sources) :
    next ≤ binding.id ∧ binding.id < next + sources.length ∧ binding.generation = binding.id := by
  unfold fresh at member
  obtain ⟨⟨source, id⟩, indexed, rfl⟩ := List.mem_map.mp member
  have lower : next ≤ id := List.le_snd_of_mem_zipIdx indexed
  have upper : id < next + sources.length := List.snd_lt_add_of_mem_zipIdx indexed
  exact ⟨lower, upper, rfl⟩

theorem fresh_covers (next : Nat) (sources : List Source) (source : Source)
    (member : source ∈ sources) :
    ∃ binding ∈ fresh next sources, binding.source = source := by
  have mapped : source ∈ (fresh next sources).map Subscription.source := by simpa using member
  exact List.mem_map.mp mapped

@[simp] theorem mem_missing (old : List Subscription) (sources : List Source) (source : Source) :
    source ∈ missing old sources ↔
      source ∈ sources ∧ ∀ binding ∈ old, binding.source ≠ source := by
  simp [missing]

theorem reconcile_retains (next : Nat) (old : List Subscription) (sources : List Source)
    (binding : Subscription) (member : binding ∈ old) (wanted : binding.source ∈ sources) :
    binding ∈ (reconcile next old sources).1 := by
  simp [reconcile, List.mem_filter, member, wanted]

theorem reconcile_sources (next : Nat) (old : List Subscription) (sources : List Source)
    (binding : Subscription) (member : binding ∈ (reconcile next old sources).1) :
    binding.source ∈ sources := by
  rcases List.mem_append.mp member with retained | added
  · exact by simpa using (List.mem_filter.mp retained).2
  · have mapped := List.mem_map_of_mem (f := Subscription.source) added
    rw [fresh_sources] at mapped
    exact (mem_missing old sources binding.source).mp mapped |>.1

theorem reconcile_covers (next : Nat) (old : List Subscription) (sources : List Source)
    (source : Source) (wanted : source ∈ sources) :
    ∃ binding ∈ (reconcile next old sources).1, binding.source = source := by
  by_cases present : ∃ binding ∈ old, binding.source = source
  · obtain ⟨binding, member, same⟩ := present
    exact ⟨binding, reconcile_retains next old sources binding member (same ▸ wanted), same⟩
  · have missing : source ∈ missing old sources := by
      rw [mem_missing]
      exact ⟨wanted, fun binding member same => present ⟨binding, member, same⟩⟩
    obtain ⟨binding, member, same⟩ := fresh_covers next _ source missing
    exact ⟨binding, List.mem_append_right _ member, same⟩

theorem reconcile_new (next : Nat) (old : List Subscription) (sources : List Source)
    (binding : Subscription) (member : binding ∈ (reconcile next old sources).1)
    (newBinding : binding ∉ old) :
    next ≤ binding.id ∧ binding.id < (reconcile next old sources).2 ∧
      binding.generation = binding.id := by
  rcases List.mem_append.mp member with retained | added
  · exact False.elim (newBinding (List.mem_filter.mp retained).1)
  · exact fresh_bounds next _ binding added

theorem reconcile_exact (next : Nat) (old : List Subscription) (sources : List Source) :
    next ≤ (reconcile next old sources).2 ∧
    (∀ binding ∈ old, binding.source ∈ sources → binding ∈ (reconcile next old sources).1) ∧
    (∀ binding ∈ (reconcile next old sources).1, binding.source ∈ sources) ∧
    (∀ source ∈ sources, ∃ binding ∈ (reconcile next old sources).1, binding.source = source) ∧
    (∀ binding ∈ (reconcile next old sources).1, binding ∉ old →
      next ≤ binding.id ∧ binding.id < (reconcile next old sources).2 ∧ binding.generation = binding.id) := by
  exact ⟨Nat.le_add_right _ _, reconcile_retains next old sources,
    reconcile_sources next old sources, reconcile_covers next old sources, reconcile_new next old sources⟩

private theorem projected_append_nodup {α β : Type} (project : α → β)
    (left right : List α) (hl : (left.map project).Nodup) (hr : (right.map project).Nodup)
    (apart : ∀ a ∈ left, ∀ b ∈ right, project a ≠ project b) :
    ((left ++ right).map project).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hl, hr, ?_⟩
  intro a ha b hb
  obtain ⟨leftValue, leftMember, rfl⟩ := List.mem_map.mp ha
  obtain ⟨rightValue, rightMember, rfl⟩ := List.mem_map.mp hb
  exact apart leftValue leftMember rightValue rightMember

theorem reconcile_valid (next : Nat) (old : List Subscription) (sources : List Source)
    (sourceUnique : (old.map Subscription.source).Nodup)
    (idUnique : (old.map Subscription.id).Nodup)
    (bounded : ∀ binding ∈ old, binding.id < next) :
    ((reconcile next old sources).1.map Subscription.source).Nodup ∧
    ((reconcile next old sources).1.map Subscription.id).Nodup ∧
    ∀ binding ∈ (reconcile next old sources).1, binding.id < (reconcile next old sources).2 := by
  let kept := old.filter (fun binding => sources.contains binding.source)
  let added := fresh next (missing old sources)
  have keptSources : (kept.map Subscription.source).Nodup :=
    sourceUnique.sublist (List.filter_sublist.map Subscription.source)
  have keptIds : (kept.map Subscription.id).Nodup :=
    idUnique.sublist (List.filter_sublist.map Subscription.id)
  have addedSources : (added.map Subscription.source).Nodup := by
    rw [fresh_sources]
    exact (unique_nodup sources).sublist List.filter_sublist
  have addedIds : (added.map Subscription.id).Nodup := by
    rw [fresh_ids]
    exact List.nodup_range'
  refine ⟨projected_append_nodup Subscription.source kept added keptSources addedSources ?_,
    projected_append_nodup Subscription.id kept added keptIds addedIds ?_, ?_⟩
  · intro a ha b hb same
    have sourceMember : b.source ∈ missing old sources := by
      have mapped := List.mem_map_of_mem (f := Subscription.source) hb
      simpa only [added, fresh_sources] using mapped
    have absent := (mem_missing old sources b.source).mp sourceMember |>.2
    exact absent a (List.mem_filter.mp ha).1 same
  · intro a ha b hb same
    have below := bounded a (List.mem_filter.mp ha).1
    have above := (fresh_bounds next _ b hb).1
    omega
  · intro binding member
    rcases List.mem_append.mp member with retained | freshMember
    · have below := bounded binding (List.mem_filter.mp retained).1
      exact Nat.lt_of_lt_of_le below (Nat.le_add_right _ _)
    · exact (fresh_bounds next _ binding freshMember).2.1

end Kotlean.Runtime.Subscriptions
