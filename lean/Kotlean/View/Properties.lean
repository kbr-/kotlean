import Kotlean.Protocol

namespace Kotlean.View

def applyProperty (property : Property) (old : Properties) : Properties := match property with
  | .text value => { old with text := value }
  | .hint value => { old with hint := value }
  | .foreground value => { old with foreground := value }
  | .background value => { old with background := value }
  | .width value => { old with width := value }
  | .height value => { old with height := value }
  | .padding value => { old with padding := value }
  | .weight value => { old with weight := value }
  | .textSize value => { old with textSize := value }
  | .enabled value => { old with enabled := value }
  | .description value => { old with description := value }
  | .alignment value => { old with alignment := value }
  | .drawing value => { old with drawing := value }
  | .listeners value => { old with listeners := value }

private def changed {α : Type} [BEq α] (old new : α) (property : Property) : List Property :=
  if equal old new then [] else [property]

private theorem mem_changed {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (old new : α) (candidate property : Property) :
    property ∈ changed old new candidate ↔ old ≠ new ∧ property = candidate := by
  by_cases same : old = new <;> simp [changed, same]

private theorem fold_slot {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (get : Properties → α)
    (set : α → Properties → Properties) (property : α → Property)
    (restore : ∀ state, set (get state) state = state)
    (interpret : ∀ value state, applyProperty (property value) state = set value state)
    (state : Properties) (value : α) :
    (changed (get state) value (property value)).foldl (fun s p => applyProperty p s) state =
      set value state := by
  by_cases same : get state = value
  · simp only [changed, equal_true, same, ite_true]
    change state = set value state
    rw [← same]
    exact (restore state).symm
  · simp only [changed, equal_true, same, ite_false]
    exact interpret value state

def allProperties (value : Properties) : List Property := [
  .text value.text, .hint value.hint, .foreground value.foreground, .background value.background,
  .width value.width, .height value.height, .padding value.padding, .weight value.weight,
  .textSize value.textSize, .enabled value.enabled, .description value.description,
  .alignment value.alignment, .drawing value.drawing, .listeners value.listeners
]

private theorem applyProperty_eq_self (property : Property) (state : Properties) :
    applyProperty property state = state ↔ property ∈ allProperties state := by
  cases property <;> cases state <;> simp [applyProperty, allProperties, eq_comm]

def diffProperties (old new : Properties) : List Property :=
  changed old.text new.text (.text new.text) ++
  changed old.hint new.hint (.hint new.hint) ++
  changed old.foreground new.foreground (.foreground new.foreground) ++
  changed old.background new.background (.background new.background) ++
  changed old.width new.width (.width new.width) ++
  changed old.height new.height (.height new.height) ++
  changed old.padding new.padding (.padding new.padding) ++
  changed old.weight new.weight (.weight new.weight) ++
  changed old.textSize new.textSize (.textSize new.textSize) ++
  changed old.enabled new.enabled (.enabled new.enabled) ++
  changed old.description new.description (.description new.description) ++
  changed old.alignment new.alignment (.alignment new.alignment) ++
  changed old.drawing new.drawing (.drawing new.drawing) ++
  changed old.listeners new.listeners (.listeners new.listeners)

def applyProperties (properties : Properties) (changes : List Property) : Properties :=
  changes.foldl (fun state property => applyProperty property state) properties

theorem diffProperties_self (properties : Properties) : diffProperties properties properties = [] := by
  simp [diffProperties, changed]

theorem apply_diffProperties (old new : Properties) :
    applyProperties old (diffProperties old new) = new := by
  simp only [applyProperties, diffProperties, List.foldl_append]
  rw [fold_slot Properties.text (fun v p => { p with text := v }) Property.text
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.hint (fun v p => { p with hint := v }) Property.hint
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.foreground (fun v p => { p with foreground := v }) Property.foreground
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.background (fun v p => { p with background := v }) Property.background
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.width (fun v p => { p with width := v }) Property.width
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.height (fun v p => { p with height := v }) Property.height
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.padding (fun v p => { p with padding := v }) Property.padding
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.weight (fun v p => { p with weight := v }) Property.weight
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.textSize (fun v p => { p with textSize := v }) Property.textSize
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.enabled (fun v p => { p with enabled := v }) Property.enabled
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.description (fun v p => { p with description := v }) Property.description
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.alignment (fun v p => { p with alignment := v }) Property.alignment
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.drawing (fun v p => { p with drawing := v }) Property.drawing
    (by intro p; cases p; rfl) (by intros; rfl)]
  rw [fold_slot Properties.listeners (fun v p => { p with listeners := v }) Property.listeners
    (by intro p; cases p; rfl) (by intros; rfl)]

theorem mem_diffProperties (old new : Properties) (property : Property) :
    property ∈ diffProperties old new ↔
      applyProperty property old ≠ old ∧ applyProperty property new = new := by
  simp only [ne_eq, applyProperty_eq_self]
  cases property <;>
    simp [diffProperties, mem_changed, allProperties, eq_comm, and_comm] <;>
    intro same <;> simp_all [eq_comm]

private theorem changed_sublist {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (old new : α) (property : Property) :
    List.Sublist (changed old new property) [property] := by
  by_cases same : old = new <;> simp [changed, same]

theorem diffProperties_sublist (old new : Properties) :
    List.Sublist (diffProperties old new) (allProperties new) := by
  have result :=
    (((((((((((((changed_sublist old.text new.text (.text new.text)).append
      (changed_sublist old.hint new.hint (.hint new.hint))).append
      (changed_sublist old.foreground new.foreground (.foreground new.foreground))).append
      (changed_sublist old.background new.background (.background new.background))).append
      (changed_sublist old.width new.width (.width new.width))).append
      (changed_sublist old.height new.height (.height new.height))).append
      (changed_sublist old.padding new.padding (.padding new.padding))).append
      (changed_sublist old.weight new.weight (.weight new.weight))).append
      (changed_sublist old.textSize new.textSize (.textSize new.textSize))).append
      (changed_sublist old.enabled new.enabled (.enabled new.enabled))).append
      (changed_sublist old.description new.description (.description new.description))).append
      (changed_sublist old.alignment new.alignment (.alignment new.alignment))).append
      (changed_sublist old.drawing new.drawing (.drawing new.drawing))).append
      (changed_sublist old.listeners new.listeners (.listeners new.listeners))
  simpa only [diffProperties, allProperties, List.cons_append, List.nil_append] using result

theorem allProperties_nodup (value : Properties) : (allProperties value).Nodup := by
  simp [allProperties]

theorem diffProperties_nodup (old new : Properties) : (diffProperties old new).Nodup :=
  List.Nodup.sublist (diffProperties_sublist old new) (allProperties_nodup new)

def propertyRank : Property → Nat
  | .text _ => 0 | .hint _ => 1 | .foreground _ => 2 | .background _ => 3
  | .width _ => 4 | .height _ => 5 | .padding _ => 6 | .weight _ => 7
  | .textSize _ => 8 | .enabled _ => 9 | .description _ => 10 | .alignment _ => 11
  | .drawing _ => 12 | .listeners _ => 13

theorem allProperties_ordered (value : Properties) :
    ((allProperties value).map propertyRank).Pairwise (· < ·) := by
  change List.Pairwise (fun a b : Nat => a < b) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  decide

theorem diffProperties_ordered (old new : Properties) :
    ((diffProperties old new).map propertyRank).Pairwise (· < ·) :=
  List.Pairwise.sublist ((diffProperties_sublist old new).map propertyRank) (allProperties_ordered new)

end Kotlean.View
