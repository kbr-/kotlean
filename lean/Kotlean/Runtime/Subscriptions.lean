module
public import Kotlean.App

@[expose] public section

namespace Kotlean.Runtime.Subscriptions

-- A timer or a platform stream runs only while the session is active; lifecycle and Back sources stay
-- installed so the app sees the session pause and resume.
def enabled (active : Bool) : Source → Bool
  | .tick _ => active
  | .platform _ _ => active
  | _ => true

def unique : List Source → List Source
  | [] => []
  | source :: sources =>
    let rest := unique sources
    if rest.contains source then rest else source :: rest

@[simp] theorem mem_unique (source : Source) (sources : List Source) :
    source ∈ unique sources ↔ source ∈ sources := by
  induction sources generalizing source with
  | nil => simp [unique]
  | cons head tail ih =>
    simp only [unique]
    split
    · rename_i present
      have member : head ∈ unique tail := by simpa using present
      simp only [List.mem_cons]
      rw [ih source]
      have original := (ih head).mp member
      constructor
      · exact Or.inr
      · rintro (rfl | found)
        · exact original
        · exact found
    · simp only [List.mem_cons, ih]

theorem unique_nodup (sources : List Source) : (unique sources).Nodup := by
  induction sources with
  | nil => simp [unique]
  | cons head tail ih =>
    simp only [unique]
    split
    · exact ih
    · rename_i absent
      simp_all

def desired (active : Bool) (declarations : List (Sub Msg)) : List Source :=
  unique ((declarations.map Sub.source).filter (enabled active))

theorem desired_exact (active : Bool) (declarations : List (Sub Msg)) :
    (desired active declarations).Nodup ∧
    ∀ source, source ∈ desired active declarations ↔
      enabled active source = true ∧ ∃ declaration ∈ declarations, declaration.source = source := by
  refine ⟨unique_nodup _, ?_⟩
  intro source
  simp only [desired, mem_unique, List.mem_filter, List.mem_map]
  exact and_comm

def missing (old : List Subscription) (sources : List Source) : List Source :=
  (unique sources).filter (fun source => !(old.any (fun binding => binding.source == source)))

def fresh (next : Nat) (sources : List Source) : List Subscription :=
  (sources.zipIdx next).map (fun (source, id) => ⟨id, id, source⟩)

def reconcile (next : Nat) (old : List Subscription) (sources : List Source) :
    List Subscription × Nat :=
  (old.filter (fun binding => sources.contains binding.source) ++ fresh next (missing old sources),
    next + (missing old sources).length)

def changes (old new : List Subscription) : List SubscriptionChange :=
  (old.filter (fun binding => !(new.contains binding))).map
    (fun binding => .remove binding.id binding.generation) ++
  (new.filter (fun binding => !(old.contains binding))).map SubscriptionChange.add

theorem changes_unchanged (bindings : List Subscription) : changes bindings bindings = [] := by
  have absent : bindings.filter (fun binding => !(bindings.contains binding)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro binding member
    simpa using member
  simp only [changes, absent, List.map_nil, List.nil_append]

def messages (source : Source) (payload : List UInt8) (declarations : List (Sub Msg)) : List Msg :=
  declarations.filterMap (fun declaration =>
    if declaration.source == source then declaration.receive payload else none)

theorem messages_exact (source : Source) (payload : List UInt8)
    (declarations : List (Sub Msg)) :
    messages source payload declarations = declarations.filterMap (fun declaration =>
      if declaration.source = source then declaration.receive payload else none) := by
  simp [messages]

def deliver (generation id : Nat) (payload : List UInt8)
    (installed : List Subscription) (declarations : List (Sub Msg)) : List Msg :=
  ((installed.find? (fun binding => binding.id == id && binding.generation == generation)).map
    (fun binding => messages binding.source payload declarations)).getD []

theorem deliver_absent (generation id : Nat) (payload : List UInt8)
    (installed : List Subscription) (declarations : List (Sub Msg))
    (absent : installed.find? (fun binding => binding.id == id && binding.generation == generation) = none) :
    deliver generation id payload installed declarations = [] := by
  simp [deliver, absent]

end Kotlean.Runtime.Subscriptions
