module
public import SnackNet.Game
public import Kotlean

@[expose] public section

namespace SnackNet
open Kotlean

structure Display where
  width : Nat := 0
  height : Nat := 0

structure Swipe where
  id : Nat
  origin : Point

structure Pad where
  display : Display := {}
  pointer : Option Nat := none
  pressed : Option Direction := none

structure Model where
  game : Game := initial
  heading : Option Direction := none
  travel : Option Direction := none
  operatorsInTransit : Option (List Operator) := none
  progress : Nat := 0
  lastFrame : Option Nat := none
  display : Display := {}
  swipe : Option Swipe := none
  pad : Pad := {}

inductive Msg where
  | key (code : Nat) (pressed : Bool)
  | touch (frame : TouchFrame)
  | padTouch (frame : TouchFrame)
  | resize (width height density : Nat)
  | padResize (width height density : Nat)
  | frame (now : Nat)
  | pause | back | restart | background

def cellTime : Nat := 190

def nextDirection (model : Model) : Option Direction :=
  let legal := fun direction => (neighbor model.game.player direction).isSome
  (model.heading.filter legal).or (model.travel.filter legal)

def advanceFrame (now : Nat) (model : Model) : Model :=
  if model.game.phase != .running then model
  else
    let elapsed := min cellTime (now - model.lastFrame.getD now)
    let model := { model with lastFrame := some now }
    let travel := if model.progress = 0 then nextDirection model else model.travel
    let plan := match model.operatorsInTransit with
      | some _ => model.operatorsInTransit
      | none => some (planOperators model.game travel)
    let progress := model.progress + elapsed
    if progress < cellTime then { model with travel, progress, operatorsInTransit := plan }
    else
      let game := tick travel model.game plan
      let operatorsArrived := model.game.beat + 1 == operatorStride
      let reset := game.lives != model.game.lives ||
        (!operatorsArrived && game.operators != model.game.operators)
      let game := if reset then { game with beat := 0 } else game
      let plan := if reset || operatorsArrived then none else plan
      let arrived := { model with game, travel, operatorsInTransit := plan }
      if game.lives != model.game.lives || game.phase != .running then
        { arrived with progress := 0, travel := none, operatorsInTransit := none }
      else
        let travel := nextDirection arrived
        let plan := if plan.isNone then some (planOperators game travel) else plan
        { arrived with progress := progress - cellTime, travel, operatorsInTransit := plan }

def frameTime (bytes : List UInt8) : Option Msg :=
  if bytes.length = 8 then
    some (.frame (bytes.foldr (fun byte time => byte.toNat + 256 * time) 0))
  else none

def keyDirection : Nat → Option Direction
  | 19 | 51 => some .up
  | 21 | 29 => some .left
  | 20 | 47 => some .down
  | 22 | 32 => some .right
  | _ => none

def swipeDirection (origin finish : Point) : Option Direction :=
  let dx := finish.x - origin.x
  let dy := finish.y - origin.y
  if max dx.natAbs dy.natAbs < 16000 then none
  else if dx.natAbs ≥ dy.natAbs then some (if dx < 0 then .left else .right)
  else some (if dy < 0 then .up else .down)

def touchUpdate (frame : TouchFrame) (model : Model) : Model :=
  match frame.phase with
  | .down =>
    if model.swipe.isSome then model
    else { model with swipe := frame.contacts.head?.map fun c => ⟨c.id, c.point⟩ }
  | .up =>
    match model.swipe, frame.contacts[frame.changed]? with
    | some swipe, some c =>
      if c.id = swipe.id then
        { model with
          swipe := none
          heading := (swipeDirection swipe.origin c.point).or model.heading }
      else model
    | _, _ => { model with swipe := none }
  | .cancel => { model with swipe := none }
  | .move => model

def directionAt (display : Display) (point : Point) : Option Direction :=
  let side := min display.width display.height * 1000
  let dx := point.x - Int.ofNat (display.width * 500)
  let dy := point.y - Int.ofNat (display.height * 500)
  if side = 0 || max dx.natAbs dy.natAbs < side * 14 / 100 then none
  else if dx.natAbs ≥ dy.natAbs then some (if dx < 0 then .left else .right)
  else some (if dy < 0 then .up else .down)

def Pad.release (pad : Pad) : Pad := { pad with pointer := none, pressed := none }

def Pad.track (pad : Pad) (contact : Contact) : Pad :=
  { pad with pointer := some contact.id, pressed := directionAt pad.display contact.point }

def padTouchUpdate (frame : TouchFrame) (model : Model) : Model :=
  let pad := model.pad
  let tracked := match frame.phase with
    | .down =>
      if pad.pointer.isSome then pad
      else (frame.contacts[frame.changed]?.map (pad.track ·)).getD pad
    | .move =>
      (frame.contacts.find? (fun contact => some contact.id == pad.pointer)).map (pad.track ·)
        |>.getD pad
    | .up =>
      if (frame.contacts[frame.changed]?.map Contact.id) == pad.pointer then pad.release else pad
    | .cancel => pad.release
  { model with pad := tracked, heading := tracked.pressed.or model.heading }

def update (message : Msg) (model : Model) : Model × List (Cmd Msg) :=
  let next : Model := match message with
    | .key code pressed =>
      if pressed then { model with heading := (keyDirection code).or model.heading } else model
    | .touch frame => touchUpdate frame model
    | .padTouch frame => padTouchUpdate frame model
    | .resize w h _ => { model with display := ⟨w, h⟩ }
    | .padResize w h _ => { model with pad := { model.pad with display := ⟨w, h⟩ } }
    | .frame now => advanceFrame now model
    | .pause | .back =>
      { model with
        game := togglePause model.game
        swipe := none
        lastFrame := none
        pad := model.pad.release }
    | .restart => { display := model.display, pad := model.pad.release }
    | .background => { model with swipe := none, lastFrame := none, pad := model.pad.release }
  (next, [])

def subscriptions (model : Model) : List (Kotlean.Sub Msg) :=
  let pause : Kotlean.Sub Msg := ⟨.pause, fun _ => some .background⟩
  if model.game.phase = .running then
    [pause, ⟨.back, fun _ => some .back⟩] ++
      if model.heading.isSome then [⟨.tick 8, frameTime⟩] else []
  else [pause]

theorem paused_has_no_timer (model : Model) (h : model.game.phase = .paused) :
    (subscriptions model).map Kotlean.Sub.source = [.pause] := by simp [subscriptions, h]

structure BoardView where
  side : Nat
  left : Nat
  top : Nat

def boardView (display : Display) : BoardView :=
  let side := min (display.width * 1000 / width) (display.height * 1000 / height)
  ⟨side, (display.width * 1000 - width * side) / 2,
    (display.height * 1000 - height * side) / 2⟩

def BoardView.point (board : BoardView) (x y : Nat) : Point :=
  ⟨Int.ofNat (board.left + x * board.side), Int.ofNat (board.top + y * board.side)⟩

def BoardView.atCell (board : BoardView) (cell : Cell) (x y : Nat) : Point :=
  let origin := board.point cell.val.1.val cell.val.2.val
  ⟨origin.x + Int.ofNat (board.side * x / 10), origin.y + Int.ofNat (board.side * y / 10)⟩

def BoardView.between (board : BoardView) (start finish : Cell) (progress : Nat)
    (duration : Nat)
    (x y : Nat) : Point :=
  let origin := board.atCell start x y
  let target := board.atCell finish x y
  let shift := fun a b => a + (b - a) * Int.ofNat progress / Int.ofNat duration
  ⟨shift origin.x target.x, shift origin.y target.y⟩

def boardTiles (board : BoardView) : List Draw :=
  (List.range height).flatMap fun y =>
    (List.range width).map fun x =>
      let color : UInt32 := if tile x y = '#' then 0xff343f6e else 0xff202841
      .rect (board.point x y) (board.side - 1000) (board.side - 1000) (board.side / 12) color

def human (board : BoardView) (atPoint : Nat → Nat → Point) (powered interceptor : Bool) :
    List Draw :=
  let s := board.side
  let coat : UInt32 := if powered then 0xffab99e9
    else if interceptor then 0xfff0788c else 0xffffb054
  [ .circle (atPoint 5 3) (s / 6) 0xffffddb4
  , .rect (atPoint 2 5) (s * 6 / 10) (s * 4 / 10) (s / 10) coat
  , .line (atPoint 5 6) (atPoint 5 8) (s / 14) 0xff22203a ]

def robot (board : BoardView) (atPoint : Nat → Nat → Point) (game : Game) : List Draw :=
  let s := board.side
  let metal : UInt32 := if game.power > 0 then 0xffd2d8e7 else 0xff47e5cb
  let face : UInt32 := if game.power > 0 then 0xff222738 else 0xff143f47
  let eye : UInt32 := if game.power > 0 then 0xffff414e else 0xffe8fffc
  [ .rect (atPoint 1 2) (s * 8 / 10) (s * 6 / 10) (s / 7) metal
  , .rect (atPoint 2 3) (s * 6 / 10) (s * 4 / 10) (s / 10) face
  , .circle (atPoint 4 5) (s / 14) eye
  , .circle (atPoint 6 5) (s / 14) eye
  , .line (atPoint 5 2) (atPoint 5 1) (s / 16) metal ]

def drawing (model : Model) : List Draw :=
  let board := boardView model.display
  let game := model.game
  let s := board.side
  let exitColor : UInt32 := if game.tokens.isEmpty then 0xff3bc8a5 else 0xff69749d
  let gate := Draw.rect (board.atCell exitCell 2 2) (s * 6 / 10) (s * 6 / 10) (s / 9) exitColor
  let tokens := game.tokens.map fun c => Draw.circle (board.atCell c 5 5) (s / 12) 0xff9ee6f2
  let pickup := if game.pickupAvailable then
    [Draw.polygon [board.atCell powerCell 5 1, board.atCell powerCell 9 5,
      board.atCell powerCell 5 9, board.atCell powerCell 1 5] 0xffffc971]
    else []
  let playerTarget := (model.travel.bind (neighbor game.player)).getD game.player
  let operators := model.operatorsInTransit.getD game.operators
  let humans := (game.operators.zip operators).flatMap fun (operator, next) =>
    let elapsed := game.beat * cellTime + model.progress
    human board (board.between operator.position next.position elapsed (operatorStride * cellTime))
      (game.power > 0) (operator.start == rightStart)
  [.clear 0xff101522] ++ boardTiles board ++ [gate] ++ tokens ++ pickup ++ humans ++
    robot board (board.between game.player playerTarget model.progress cellTime) game

def button (label : String) (message : Msg) : Ui Msg :=
  .button {
    text := label, width := .wrap, height := .dp 48, padding := 14
    background := 0xff304063, events := { click := some message } }

def padDrawing (pad : Pad) : List Draw :=
  let side := min pad.display.width pad.display.height * 1000
  let size := fun n : Nat => side * n / 100
  let originX := (pad.display.width * 1000 - side) / 2
  let originY := (pad.display.height * 1000 - side) / 2
  let point := fun x y => Point.mk (Int.ofNat (originX + size x)) (Int.ofNat (originY + size y))
  let plate := fun x y w h r color => Draw.rect (point x y) (size w) (size h) (size r) color
  let arm := fun (direction : Direction) x y a b c d e f =>
    let pressed := pad.pressed == some direction
    let tint : UInt32 := if pressed then 0xff183f4d else 0xff212f4b
    let ink : UInt32 := if pressed then 0xff66f2d8 else 0xffb9c8e6
    [ plate x y 24 24 6 tint
    , Draw.line (point a b) (point c d) (size 2) ink
    , Draw.line (point c d) (point e f) (size 2) ink ]
  [ .clear 0xff101522
  , plate 32 5 36 94 12 0xff080e19
  , plate 3 34 94 36 12 0xff080e19
  , plate 32 3 36 94 12 0xff3c4e70
  , plate 3 32 94 36 12 0xff3c4e70
  , plate 33 4 34 92 11 0xff19253b
  , plate 4 33 92 34 11 0xff19253b
  , .circle (point 50 50) (size 10) 0xff121e31
  , .circle (point 50 50) (size 3) 0xff4b6384 ] ++
    arm .up 38 7 44 23 50 16 56 23 ++
    arm .left 7 38 23 44 16 50 23 56 ++
    arm .right 69 38 77 44 84 50 77 56 ++
    arm .down 38 69 44 77 50 84 56 77

def directionPad (pad : Pad) : Ui Msg :=
  .row { width := .fill, alignment := .center }
    [ .canvas {
      width := .dp 166, height := .dp 166, drawing := padDrawing pad
      description := "Directional pad"
      events := { touch := some .padTouch, resize := some .padResize } } ]

def status (model : Model) : String :=
  let game := model.game
  match game.phase with
  | .won => "Network secured"
  | .lost => "Signal lost"
  | .paused => "Paused"
  | .running =>
    if model.heading.isNone then "Swipe or use the D-pad"
    else if game.power > 0 then s!"OVERCLOCK  {game.power}"
    else if game.tokens.isEmpty then "Exit open"
    else s!"{game.tokens.length} tokens left"

def view (model : Model) : Ui Msg :=
  .column { width := .fill, height := .fill, background := 0xff101522, padding := 12 }
    [ .text { text := "SnackNet", textSize := 25, foreground := 0xff47e5cb }
    , .text {
        text := s!"Score {score model.game}   Lives {model.game.lives.val}   {status model}",
        textSize := 16, padding := 6 }
    , .canvas {
        width := .fill, height := .dp 0, weight := 1
        description := "SnackNet maze. Swipe or use the direction keys to steer."
        drawing := drawing model
        events := { touch := some .touch, key := some .key, resize := some .resize } }
    , directionPad model.pad
    , .row { width := .fill, alignment := .center, padding := 4 }
        [button (if model.game.phase = .paused then "Resume" else "Pause") .pause,
         button "Restart" .restart] ]

def app : App := {
  Model := Model
  Msg := Msg
  init := ({}, [])
  update := update
  view := view
  subscriptions := subscriptions
}

end SnackNet
