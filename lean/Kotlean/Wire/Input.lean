module
public import Kotlean.Protocol
public import Kotlean.Wire.Checked
public import Kotlean.Wire.Scalar
public import Kotlean.Wire.Frame

@[expose] public section

namespace Kotlean.Wire

def envelope : Codec (UInt8 × List UInt8) := pair byte (list byte)

def kindValue : NodeKind → UInt8 × List UInt8
  | .column => (0, []) | .row => (1, []) | .text => (2, []) | .button => (3, [])
  | .input => (4, []) | .scroll => (5, []) | .canvas => (6, [])

def parseKind (value : UInt8 × List UInt8) : Option NodeKind :=
  if value.1 = 0 then some .column else if value.1 = 1 then some .row
  else if value.1 = 2 then some .text else if value.1 = 3 then some .button
  else if value.1 = 4 then some .input else if value.1 = 5 then some .scroll
  else if value.1 = 6 then some .canvas else none

def nodeKind : Codec NodeKind := checked envelope kindValue parseKind
  (by intro value; cases value <;> decide)

def phaseValue : TouchPhase → UInt8 × List UInt8
  | .down => (0, []) | .move => (1, []) | .up => (2, []) | .cancel => (3, [])

def parsePhase (value : UInt8 × List UInt8) : Option TouchPhase :=
  if value.1 = 0 then some .down else if value.1 = 1 then some .move
  else if value.1 = 2 then some .up else if value.1 = 3 then some .cancel else none

def touchPhase : Codec TouchPhase := checked envelope phaseValue parsePhase
  (by intro value; cases value <;> decide)

def point : Codec Point := adapt (pair signed signed)
  (fun value => (value.x, value.y)) (fun value => some ⟨value.1, value.2⟩)
  (by intro value; cases value; rfl)
  (by intro raw value accepted; cases accepted; rfl)

def contact : Codec Contact := adapt (pair natural point)
  (fun value => (value.id, value.point)) (fun value => some ⟨value.1, value.2⟩)
  (by intro value; cases value; rfl)
  (by intro raw value accepted; cases accepted; rfl)

def touchFrame : Codec TouchFrame :=
  adapt (pair touchPhase (pair natural (pair natural (list contact))))
    (fun value => (value.phase, value.changed, value.milliseconds, value.contacts))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)
    (by intro raw value accepted; cases accepted; rfl)

def inputValue : Input → UInt8 × List UInt8
  | .click => (0, [])
  | .text value => (1, text.write value)
  | .touch value => (2, touchFrame.write value)
  | .key code down => (3, (pair natural boolean).write (code, down))
  | .resize width height density =>
    (4, (pair natural (pair natural natural)).write (width, height, density))

def parseInput (value : UInt8 × List UInt8) : Option Input :=
  if value.1 = 0 then some .click
  else if value.1 = 1 then (decode text value.2).map Input.text
  else if value.1 = 2 then (decode touchFrame value.2).map Input.touch
  else if value.1 = 3 then
    (decode (pair natural boolean) value.2).map fun data => .key data.1 data.2
  else if value.1 = 4 then
    (decode (pair natural (pair natural natural)) value.2).map fun data =>
      .resize data.1 data.2.1 data.2.2
  else none

def input : Codec Input := checked envelope inputValue parseInput
  (by
    intro value
    cases value <;> simp [inputValue, parseInput, decode_write])

end Kotlean.Wire
