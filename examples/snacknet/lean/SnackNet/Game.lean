module
public import Std

@[expose] public section

namespace SnackNet

abbrev width : Nat := 11
abbrev height : Nat := 9

def maze : Array (Array Char) := #[
    #['#', '#', '#', '#', '#', '#', '#', '#', '#', '#', '#'],
    #['#', 'S', '*', '.', '#', '.', '.', '*', '*', 'E', '#'],
    #['#', '.', '#', '.', '#', '.', '#', '#', '.', '.', '#'],
    #['#', '.', '#', '*', '*', '.', '#', '.', '.', '.', '#'],
    #['#', '*', '.', '.', '#', '.', '#', '.', '#', '.', '#'],
    #['#', '#', '#', '.', '#', '*', '.', '.', '#', '.', '#'],
    #['#', '.', '.', '.', '#', '#', '#', '.', '#', '.', '#'],
    #['#', 'O', '*', '.', '.', 'P', '*', '.', '.', 'O', '#'],
    #['#', '#', '#', '#', '#', '#', '#', '#', '#', '#', '#']]

def tile (x y : Nat) : Char := (maze[y]?.getD #[])[x]?.getD '#'

abbrev GridPoint := Fin width × Fin height
abbrev Cell := { p : GridPoint // tile p.1.val p.2.val ≠ '#' }

def cellAt (x y : Nat) : Option Cell :=
  if hx : x < width then
    if hy : y < height then
      if openTile : tile x y ≠ '#' then some ⟨(⟨x, hx⟩, ⟨y, hy⟩), openTile⟩ else none
    else none
  else none

def playerStart : Cell := ⟨(1, 1), by decide +kernel⟩
def leftStart : Cell := ⟨(1, 7), by decide +kernel⟩
def rightStart : Cell := ⟨(9, 7), by decide +kernel⟩
def exitCell : Cell := ⟨(9, 1), by decide +kernel⟩
def powerCell : Cell := ⟨(5, 7), by decide +kernel⟩

def initialTokens : List Cell :=
  (List.range height).flatMap fun y =>
    (List.range width).filterMap fun x => if tile x y == '*' then cellAt x y else none

inductive Direction where
  | up | left | down | right
  deriving DecidableEq, Repr

def directions : List Direction := [.up, .left, .down, .right]

def neighbor (cell : Cell) (direction : Direction) : Option Cell :=
  let x := cell.val.1.val
  let y := cell.val.2.val
  match direction with
  | .up => if y = 0 then none else cellAt x (y - 1)
  | .left => if x = 0 then none else cellAt (x - 1) y
  | .down => cellAt x (y + 1)
  | .right => cellAt (x + 1) y

def distance (a b : Cell) : Nat :=
  let (ax, ay) := a.val
  let (bx, row) := b.val
  (ax.val - bx.val) + (bx.val - ax.val) + (ay.val - row.val) + (row.val - ay.val)

structure Operator where
  start : Cell
  position : Cell
  deriving DecidableEq

inductive Phase where
  | running | paused | won | lost
  deriving DecidableEq, Repr

structure Game where
  player : Cell
  operators : List Operator
  tokens : List Cell
  lives : Fin 4
  power : Nat
  pickupAvailable : Bool
  beat : Nat
  phase : Phase
  deriving DecidableEq

def initial : Game :=
  ⟨playerStart, [⟨leftStart, leftStart⟩, ⟨rightStart, rightStart⟩], initialTokens,
    3, 0, true, 0, .running⟩

def score (game : Game) : Nat := 10 * (initialTokens.length - game.tokens.length)

def moveOperator (player : Cell) (powered : Bool) (operator : Operator) : Operator :=
  let options := directions.filterMap (neighbor operator.position)
  let better (candidate best : Cell) : Bool :=
    if powered then distance best player < distance candidate player
    else distance candidate player < distance best player
  let position := match options with
    | [] => operator.position
    | first :: rest => rest.foldl (fun best candidate => if better candidate best then candidate else best) first
  { operator with position }

def contact (game : Game) : Bool :=
  game.operators.any fun operator => decide (operator.position = game.player)

def settle (game : Game) : Game :=
  if contact game then
    if game.power > 0 then
      { game with operators := game.operators.map fun operator =>
          if operator.position = game.player then { operator with position := operator.start }
          else operator }
    else
      let lives : Fin 4 := ⟨game.lives.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) game.lives.isLt⟩
      { game with
        player := playerStart
        lives := lives
        operators := game.operators.map fun operator => { operator with position := operator.start }
        phase := if lives.val = 0 then .lost else .running }
  else game

def moveActors (game : Game) : Game :=
  if contact game then settle game
  else if game.beat = 2 then
    settle { game with operators := game.operators.map (moveOperator game.player (game.power > 0)) }
  else game

def tick (direction : Option Direction) (game : Game) : Game :=
  if game.phase = .running then
    let player := (direction.bind (neighbor game.player)).getD game.player
    let pickup := game.pickupAvailable && decide (player = powerCell)
    let moved := moveActors { game with
      player := player
      tokens := game.tokens.filter fun token => decide (token ≠ player)
      power := if pickup then 24 else game.power
      pickupAvailable := game.pickupAvailable && !pickup }
    { moved with
      power := moved.power - 1
      beat := (moved.beat + 1) % 3
      phase := if moved.phase = .running ∧ moved.tokens.isEmpty ∧ moved.player = exitCell
        then .won else moved.phase }
  else game

def togglePause (game : Game) : Game :=
  match game.phase with
  | .running => { game with phase := .paused }
  | .paused => { game with phase := .running }
  | .won | .lost => game

def restart (_ : Game) : Game := initial

theorem cell_bounds (cell : Cell) : cell.val.1.val < width ∧ cell.val.2.val < height :=
  ⟨cell.val.1.isLt, cell.val.2.isLt⟩

theorem cell_open (cell : Cell) : tile cell.val.1.val cell.val.2.val ≠ '#' := cell.property

theorem cellAt_coordinates {x y : Nat} {cell : Cell} (h : cellAt x y = some cell) :
    cell.val.1.val = x ∧ cell.val.2.val = y := by
  unfold cellAt at h
  split at h
  · split at h
    · split at h
      · cases h
        exact ⟨rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem neighbor_one {origin target : Cell} {direction : Direction}
    (h : neighbor origin direction = some target) : distance origin target = 1 := by
  cases origin with
  | mk point openTile =>
    cases point with
    | mk x y =>
      cases target with
      | mk point openTarget =>
        cases point with
        | mk u v =>
          cases direction <;> simp only [neighbor] at h
          · split at h
            · cases h
            · obtain ⟨hu, hv⟩ := cellAt_coordinates h
              simp only [distance] at *
              omega
          · split at h
            · cases h
            · obtain ⟨hu, hv⟩ := cellAt_coordinates h
              simp only [distance] at *
              omega
          · obtain ⟨hu, hv⟩ := cellAt_coordinates h
            simp only [distance] at *
            omega
          · obtain ⟨hu, hv⟩ := cellAt_coordinates h
            simp only [distance] at *
            omega

theorem paused_tick (game : Game) (direction : Option Direction) (h : game.phase = .paused) :
    tick direction game = game := by simp [tick, h]

theorem finished_tick (game : Game) (direction : Option Direction) (h : game.phase ≠ .running) :
    tick direction game = game := by simp [tick, h]

theorem powered_contact_lives (game : Game) (h : 0 < game.power) :
    (settle game).lives = game.lives := by
  unfold settle
  split <;> simp_all

theorem settle_tokens (game : Game) : (settle game).tokens = game.tokens := by
  unfold settle
  split <;> try rfl
  split <;> rfl

theorem moveActors_tokens (game : Game) : (moveActors game).tokens = game.tokens := by
  unfold moveActors
  split
  · exact settle_tokens game
  · split
    · rw [settle_tokens]
    · rfl

theorem moveActors_powered_lives (game : Game) (h : 0 < game.power) :
    (moveActors game).lives = game.lives := by
  unfold moveActors
  split
  · exact powered_contact_lives game h
  · split
    · exact powered_contact_lives _ h
    · rfl

theorem tick_powered_lives (direction : Option Direction) (game : Game) (h : 0 < game.power) :
    (tick direction game).lives = game.lives := by
  unfold tick
  split
  · apply moveActors_powered_lives
    split <;> simp_all
  · rfl

theorem tick_tokens (direction : Option Direction) (game : Game) :
    (tick direction game).tokens.length ≤ game.tokens.length := by
  unfold tick
  split
  · simp only [moveActors_tokens]
    exact List.length_filter_le ..
  · exact Nat.le_refl _

theorem lives_bound (game : Game) : game.lives.val ≤ 3 := Nat.le_of_lt_succ game.lives.isLt

theorem play_tokens (moves : List (Option Direction)) (game : Game) :
    (moves.foldl (fun state direction => tick direction state) game).tokens.length ≤ game.tokens.length := by
  induction moves generalizing game with
  | nil => exact Nat.le_refl _
  | cons direction rest ih =>
    exact Nat.le_trans (ih (tick direction game)) (tick_tokens direction game)

end SnackNet
