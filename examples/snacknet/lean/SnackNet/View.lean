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

structure Model where
  game : Game := initial
  heading : Option Direction := none
  display : Display := {}
  swipe : Option Swipe := none

inductive Msg where
  | steer (direction : Direction)
  | key (code : Nat) (pressed : Bool)
  | touch (frame : TouchFrame)
  | resize (width height density : Nat)
  | tick | pause | back | restart | background

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

def update (message : Msg) (model : Model) : Model × List (Cmd Msg) :=
  let next : Model := match message with
    | .steer direction => { model with heading := some direction }
    | .key code pressed =>
      if pressed then { model with heading := (keyDirection code).or model.heading } else model
    | .touch frame => touchUpdate frame model
    | .resize w h _ => { model with display := ⟨w, h⟩ }
    | .tick =>
      if model.heading.isSome then { model with game := tick model.heading model.game } else model
    | .pause | .back => { model with game := togglePause model.game, swipe := none }
    | .restart => { display := model.display }
    | .background => { model with swipe := none }
  (next, [])

def subscriptions (model : Model) : List (Kotlean.Sub Msg) :=
  let pause : Kotlean.Sub Msg := ⟨.pause, fun _ => some .background⟩
  if model.game.phase = .running then
    [pause, ⟨.back, fun _ => some .back⟩] ++
      if model.heading.isSome then [⟨.tick 190, fun _ => some .tick⟩] else []
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

def boardTiles (board : BoardView) : List Draw :=
  (List.range height).flatMap fun y =>
    (List.range width).map fun x =>
      let color : UInt32 := if tile x y = '#' then 0xff343f6e else 0xff202841
      .rect (board.point x y) (board.side - 1000) (board.side - 1000) (board.side / 12) color

def human (board : BoardView) (operator : Operator) (powered : Bool) : List Draw :=
  let cell := operator.position
  let s := board.side
  let coat : UInt32 := if powered then 0xffab99e9 else 0xffffb054
  [ .circle (board.atCell cell 5 3) (s / 6) 0xffffddb4
  , .rect (board.atCell cell 2 5) (s * 6 / 10) (s * 4 / 10) (s / 10) coat
  , .line (board.atCell cell 5 6) (board.atCell cell 5 8) (s / 14) 0xff22203a ]

def robot (board : BoardView) (game : Game) : List Draw :=
  let cell := game.player
  let s := board.side
  let metal : UInt32 := if game.power > 0 then 0xffd2d8e7 else 0xff47e5cb
  let face : UInt32 := if game.power > 0 then 0xff222738 else 0xff143f47
  let eye : UInt32 := if game.power > 0 then 0xffff414e else 0xffe8fffc
  [ .rect (board.atCell cell 1 2) (s * 8 / 10) (s * 6 / 10) (s / 7) metal
  , .rect (board.atCell cell 2 3) (s * 6 / 10) (s * 4 / 10) (s / 10) face
  , .circle (board.atCell cell 4 5) (s / 14) eye
  , .circle (board.atCell cell 6 5) (s / 14) eye
  , .line (board.atCell cell 5 2) (board.atCell cell 5 1) (s / 16) metal ]

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
  [.clear 0xff101522] ++ boardTiles board ++ [gate] ++ tokens ++ pickup ++
    game.operators.flatMap (human board · (game.power > 0)) ++ robot board game

def button (label : String) (message : Msg) : Ui Msg :=
  .button {
    text := label, width := .wrap, height := .dp 48, padding := 14
    background := 0xff304063, events := { click := some message } }

def status (model : Model) : String :=
  let game := model.game
  match game.phase with
  | .won => "Network secured"
  | .lost => "Signal lost"
  | .paused => "Paused"
  | .running =>
    if model.heading.isNone then "Swipe or tap an arrow"
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
    , .row { width := .fill, alignment := .center, padding := 4 }
        [button "←" (.steer .left), button "↑" (.steer .up),
         button "↓" (.steer .down), button "→" (.steer .right)]
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
