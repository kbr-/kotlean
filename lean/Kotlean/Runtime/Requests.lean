module
public import Kotlean.App

@[expose] public section

namespace Kotlean.Runtime

def consume (id : Nat) (pending : Pending Msg) :
    Option (Reply → Option Msg) × Pending Msg :=
  (pending[id]?, pending.erase id)

def issue (next : Nat) (pending : Pending Msg) (command : Cmd Msg) :
    Command × Nat × Pending Msg :=
  (⟨next, command.effect⟩, next + 1, match command.answer with
    | none => pending.erase next
    | some answer => pending.insert next answer)

theorem consume_selected (id : Nat) (pending : Pending Msg) :
    (consume id pending).1 = pending[id]? ∧
    (consume id pending).2[id]? = none ∧
    ∀ other, other ≠ id → (consume id pending).2[other]? = pending[other]? := by
  refine ⟨rfl, by simp [consume], ?_⟩
  intro other different
  simp [consume, Std.ExtTreeMap.getElem?_erase, Ne.symm different]

theorem issue_selected (next : Nat) (pending : Pending Msg) (command : Cmd Msg) :
    (issue next pending command).1.id = next ∧
    (issue next pending command).1.effect = command.effect ∧
    (issue next pending command).2.1 = next + 1 ∧
    (issue next pending command).2.2[next]? = command.answer ∧
    ∀ other, other ≠ next → (issue next pending command).2.2[other]? = pending[other]? := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · cases h : command.answer <;> simp [issue, h]
  · intro other different
    cases h : command.answer <;>
      simp [issue, h, Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert,
        Ne.symm different]

theorem issue_bounded (next : Nat) (pending : Pending Msg) (command : Cmd Msg)
    (bounded : ∀ id, (pending[id]?).isSome → id < next) :
    ∀ id, ((issue next pending command).2.2[id]?).isSome →
      id < (issue next pending command).2.1 := by
  intro id present
  have selected := issue_selected next pending command
  rw [selected.2.2.1]
  by_cases same : id = next
  · omega
  · rw [selected.2.2.2.2 id same] at present
    have := bounded id present
    omega

theorem consume_bounded (next : Nat) (pending : Pending Msg) (id : Nat)
    (bounded : ∀ key, (pending[key]?).isSome → key < next) :
    ∀ key, ((consume id pending).2[key]?).isSome → key < next := by
  intro key present
  by_cases same : key = id
  · subst key
    rw [(consume_selected id pending).2.1] at present
    contradiction
  · rw [(consume_selected id pending).2.2 key same] at present
    exact bounded key present

theorem consume_twice (id : Nat) (pending : Pending Msg) :
    (consume id (consume id pending).2).1 = none := by
  exact (consume_selected id pending).2.1

def initial (app : App) (input : InitInput) : app.Model × List (Cmd app.Msg) :=
  match input.snapshot, app.persistence with
  | some bytes, some persistence => match persistence.restore bytes with
    | some model => (model, [])
    | none => app.init
  | _, _ => app.init

def snapshot (app : App) (model : app.Model) : Option (List UInt8) :=
  app.persistence.map (fun persistence => persistence.save model)

theorem initial_choice (app : App) (input : InitInput) :
    initial app input = match input.snapshot, app.persistence with
      | some bytes, some persistence => match persistence.restore bytes with
        | some model => (model, [])
        | none => app.init
      | _, _ => app.init := rfl

theorem snapshot_choice (app : App) (model : app.Model) :
    snapshot app model = app.persistence.map (fun persistence => persistence.save model) := rfl

end Kotlean.Runtime
