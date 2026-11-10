module
@[expose] public section

namespace Kotlean

def equal [BEq α] (left right : α) : Bool := left == right

@[simp] theorem equal_true [BEq α] [LawfulBEq α] (left right : α) :
    equal left right = true ↔ left = right := by
  simp [equal]

theorem equal_eq_decide [BEq α] [LawfulBEq α] [DecidableEq α] (left right : α) :
    equal left right = decide (left = right) := by
  by_cases h : left = right <;> simp [equal, h]

theorem equality_context [BEq α] [LawfulBEq α] [DecidableEq α]
    (left right : α) (context : Bool → β) :
    context (equal left right) = context (decide (left = right)) := by
  rw [equal_eq_decide]

theorem equality_program [BEq α] [LawfulBEq α] [DecidableEq α]
    (program : (α → α → Bool) → β) :
    program equal = program (fun left right => decide (left = right)) := by
  have h : (fun left right : α => equal left right) =
      (fun left right => decide (left = right)) := by
    funext left right
    exact equal_eq_decide left right
  exact congrArg program h

end Kotlean
