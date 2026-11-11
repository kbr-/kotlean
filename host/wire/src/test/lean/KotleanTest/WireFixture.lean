import Kotlean

namespace KotleanTest.WireFixture

open Kotlean Kotlean.Wire

def payload (n : Nat) : List UInt8 :=
  (List.range (n % 5)).map fun i => UInt8.ofNat (n + 7 * i)

def label (n : Nat) : String := "λ🤖/" ++ toString n

def position (n : Nat) : Point := ⟨Int.ofNat n, -Int.ofNat (n + 1)⟩

def flag (n bit : Nat) : Bool := n / (2 ^ bit) % 2 == 1

def kind (n : Nat) : NodeKind := match n % 7 with
  | 0 => .column | 1 => .row | 2 => .text | 3 => .button
  | 4 => .input | 5 => .scroll | _ => .canvas

def phase (n : Nat) : TouchPhase := match n % 4 with
  | 0 => .down | 1 => .move | 2 => .up | _ => .cancel

def dimension (n : Nat) : Dimension := match n % 3 with
  | 0 => .wrap | 1 => .fill | _ => .dp (n + 2)

def align (n : Nat) : Alignment := match n % 3 with
  | 0 => .start | 1 => .center | _ => .finish

def source (n : Nat) : Source := match n % 5 with
  | 0 => .tick (n + 1) | 1 => .back | 2 => .pause | 3 => .resume
  | _ => .platform (label n) (payload n)

def mask (n : Nat) : ListenerMask :=
  ⟨flag n 0, flag n 1, flag n 2, flag n 3, flag n 4⟩

def drawing (n : Nat) : List Draw := [
  .clear (UInt32.ofNat n),
  .rect (position n) (n + 2) (n + 3) (n + 4) (UInt32.ofNat (n + 5)),
  .circle (position (n + 1)) (n + 6) (UInt32.ofNat (n + 7)),
  .line (position n) (position (n + 1)) (n + 8) (UInt32.ofNat (n + 9)),
  .polygon ((List.range (n % 4)).map fun i => position (n + i)) (UInt32.ofNat (n + 10)),
  .text (position (n + 2)) (n + 11) (label n) (UInt32.ofNat (n + 12))
]

def property (n : Nat) : Property := match n % 14 with
  | 0 => .text (label n) | 1 => .hint (label (n + 1))
  | 2 => .foreground (UInt32.ofNat n) | 3 => .background (UInt32.ofNat (n + 1))
  | 4 => .width (dimension n) | 5 => .height (dimension (n + 1))
  | 6 => .padding (n + 2) | 7 => .weight (n + 3) | 8 => .textSize (n + 4)
  | 9 => .enabled (flag n 0) | 10 => .description (label n)
  | 11 => .alignment (align n) | 12 => .drawing (drawing n) | _ => .listeners (mask n)

def input (n : Nat) : Input := match n % 5 with
  | 0 => .click
  | 1 => .text (label n)
  | 2 => .touch ⟨phase n, n % 3, n + 2 ^ 64,
      (List.range (n % 4)).map fun i => ⟨n + 7 * i, position (n + i)⟩⟩
  | 3 => .key (n + 2 ^ 64) (flag n 0)
  | _ => .resize (n + 1) (n + 2) (n + 3)

def event (seed : UInt64) : Event :=
  let n := seed.toNat
  match n % 5 with
  | 0 => .node (n + 2 ^ 64) (n + 17) (input (n / 5))
  | 1 => .answer (n + 19) (if flag (n / 5) 0 then .error (label n) else .ok (payload n))
  | 2 => .subscription (7 * n + 1) (11 * n + 2) (payload n)
  | 3 => .lifecycle (flag n 0)
  | _ => .save

def effects (n : Nat) : List Effect := [
  .delay (n + 1), .read (label n), .write (label (n + 1)) (payload n), .log (label (n + 2)),
  .haptic, .clipboard (label (n + 3)), .platform (label (n + 4)) (payload (n + 1))
]

def commands (n : Nat) : List Command :=
  (effects n).zipIdx.map fun (effect, i) => ⟨n + 100 + i, effect⟩

def output (seed : UInt64) : Out :=
  let n := seed.toNat
  match n % 3 with
  | 0 => .changes ⟨n + 2 ^ 64,
      [.create n (kind n), .property n (property (n / 3)),
        .property n (.drawing (drawing n)), .property n (.listeners (mask n)),
        .insert n (n + 1) (n + 2), .remove (n + 3),
        .root (if flag n 0 then some n else none)],
      commands n, [.add ⟨n + 11, n + 13, source n⟩, .remove (n + 11) (n + 12)],
      if flag n 2 then some (payload n) else none⟩
  | 1 => .ignored (if flag n 1 then some (label n) else none)
  | _ => .failed (label n)

def initial (seed : UInt64) : InitInput :=
  ⟨if flag seed.toNat 0 then some (payload seed.toNat) else none⟩

@[export kotlean_test_matches_event]
def matchesEvent (seed : UInt64) (bytes : ByteArray) : UInt8 :=
  if equal (decodeBytes Kotlean.Wire.event bytes) (some (event seed)) then 1 else 0

@[export kotlean_test_matches_init]
def matchesInit (seed : UInt64) (bytes : ByteArray) : UInt8 :=
  if equal (decodeBytes initInput bytes) (some (initial seed)) then 1 else 0

@[export kotlean_test_output]
def outputBytes (seed : UInt64) : ByteArray := encodeBytes out (output seed)

@[export kotlean_test_accepts_out]
def acceptsOut (bytes : ByteArray) : UInt8 :=
  if (decodeBytes out bytes).isSome then 1 else 0

@[export kotlean_test_accepts_event]
def acceptsEvent (bytes : ByteArray) : UInt8 :=
  if (decodeBytes Kotlean.Wire.event bytes).isSome then 1 else 0

@[export kotlean_test_echo]
def echo (bytes : ByteArray) : ByteArray := bytes

theorem event_fixture (seed : UInt64) :
    matchesEvent seed (encodeBytes Kotlean.Wire.event (event seed)) = 1 := by
  simp [matchesEvent, decodeBytes_encodeBytes]

theorem init_fixture (seed : UInt64) :
    matchesInit seed (encodeBytes initInput (initial seed)) = 1 := by
  simp [matchesInit, decodeBytes_encodeBytes]

theorem output_fixture (seed : UInt64) : acceptsOut (outputBytes seed) = 1 := by
  simp [acceptsOut, outputBytes, decodeBytes_encodeBytes]

theorem encoded_event_accepted (value : Event) :
    acceptsEvent (encodeBytes Kotlean.Wire.event value) = 1 := by
  simp [acceptsEvent, decodeBytes_encodeBytes]

theorem echo_preserves (bytes : ByteArray) : echo bytes = bytes := rfl

end KotleanTest.WireFixture
