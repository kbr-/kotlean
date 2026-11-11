module
public import Kotlean.Equality

@[expose] public section

namespace Kotlean

inductive NodeKind where
  | column | row | text | button | input | scroll | canvas
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive TouchPhase where
  | down | move | up | cancel
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Point where
  x : Int
  y : Int
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Contact where
  id : Nat
  point : Point
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure TouchFrame where
  phase : TouchPhase
  changed : Nat
  milliseconds : Nat
  contacts : List Contact
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Input where
  | click
  | text (value : String)
  | touch (frame : TouchFrame)
  | key (code : Nat) (down : Bool)
  | resize (width height density : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Source where
  | tick (milliseconds : Nat)
  | back | pause | resume
  | platform (name : String) (payload : List UInt8)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Reply where
  | ok (payload : List UInt8)
  | error (message : String)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Event where
  | node (revision id : Nat) (input : Input)
  | answer (id : Nat) (reply : Reply)
  | subscription (generation id : Nat) (payload : List UInt8)
  | lifecycle (active : Bool)
  | save
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Effect where
  | delay (milliseconds : Nat)
  | read (key : String)
  | write (key : String) (value : List UInt8)
  | log (text : String)
  | haptic
  | clipboard (text : String)
  | platform (name : String) (payload : List UInt8)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Command where
  id : Nat
  effect : Effect
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Subscription where
  id : Nat
  generation : Nat
  source : Source
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Dimension where
  | wrap
  | fill
  | dp (value : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Alignment where
  | start | center | finish
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Draw where
  | clear (color : UInt32)
  | rect (origin : Point) (width height radius : Nat) (color : UInt32)
  | circle (center : Point) (radius : Nat) (color : UInt32)
  | line (start finish : Point) (width : Nat) (color : UInt32)
  | polygon (points : List Point) (color : UInt32)
  -- `alignment` places the text's start, centre or end at `origin`; `weight` is a font weight from
  -- 100 to 900, 400 regular.
  | text (origin : Point) (size : Nat) (value : String) (color : UInt32)
      (alignment : Alignment := .start) (weight : Nat := 400)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure ListenerMask where
  click : Bool := false
  text : Bool := false
  touch : Bool := false
  key : Bool := false
  resize : Bool := false
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Properties where
  text : String := ""
  hint : String := ""
  foreground : UInt32 := 0xffffffff
  background : UInt32 := 0
  width : Dimension := .wrap
  height : Dimension := .wrap
  padding : Nat := 0
  weight : Nat := 0
  textSize : Nat := 16
  enabled : Bool := true
  description : String := ""
  alignment : Alignment := .start
  drawing : List Draw := []
  listeners : ListenerMask := {}
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Property where
  | text (value : String)
  | hint (value : String)
  | foreground (value : UInt32)
  | background (value : UInt32)
  | width (value : Dimension)
  | height (value : Dimension)
  | padding (value : Nat)
  | weight (value : Nat)
  | textSize (value : Nat)
  | enabled (value : Bool)
  | description (value : String)
  | alignment (value : Alignment)
  | drawing (value : List Draw)
  | listeners (value : ListenerMask)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Patch where
  | create (id : Nat) (kind : NodeKind)
  | property (id : Nat) (value : Property)
  | insert (parent index child : Nat)
  | remove (id : Nat)
  | root (id : Option Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive SubscriptionChange where
  | add (subscription : Subscription)
  | remove (id generation : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Output where
  revision : Nat
  patches : List Patch
  commands : List Command
  subscriptions : List SubscriptionChange
  snapshot : Option (List UInt8)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Out where
  | changes (value : Output)
  | ignored (diagnostic : Option String)
  | failed (message : String)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure InitInput where
  snapshot : Option (List UInt8)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

end Kotlean
