module
public import Kotlean.Wire.Input
public import Kotlean.Wire.Option

@[expose] public section

namespace Kotlean.Wire

def dimensionValue : Dimension → UInt8 × List UInt8
  | .wrap => (0, []) | .fill => (1, []) | .dp value => (2, natural.write value)

def parseDimension (value : UInt8 × List UInt8) : Option Dimension :=
  if value.1 = 0 then some .wrap else if value.1 = 1 then some .fill
  else if value.1 = 2 then (decode natural value.2).map Dimension.dp else none

def dimension : Codec Dimension := checked envelope dimensionValue parseDimension
  (by intro value; cases value <;> simp [dimensionValue, parseDimension, decode_write])

def alignmentValue : Alignment → UInt8 × List UInt8
  | .start => (0, []) | .center => (1, []) | .finish => (2, [])

def parseAlignment (value : UInt8 × List UInt8) : Option Alignment :=
  if value.1 = 0 then some .start else if value.1 = 1 then some .center
  else if value.1 = 2 then some .finish else none

def alignment : Codec Alignment := checked envelope alignmentValue parseAlignment
  (by intro value; cases value <;> decide)

def rectFields := pair point (pair natural (pair natural (pair natural color)))
def circleFields := pair point (pair natural color)
def lineFields := pair point (pair point (pair natural color))
def polygonFields := pair (list point) color
def textFields := pair point (pair natural (pair text color))

def drawValue : Draw → UInt8 × List UInt8
  | .clear value => (0, color.write value)
  | .rect p width height radius value => (1, rectFields.write (p, width, height, radius, value))
  | .circle p radius value => (2, circleFields.write (p, radius, value))
  | .line start finish width value => (3, lineFields.write (start, finish, width, value))
  | .polygon points value => (4, polygonFields.write (points, value))
  | .text p size value paint => (5, textFields.write (p, size, value, paint))

def parseDraw (value : UInt8 × List UInt8) : Option Draw :=
  if value.1 = 0 then (decode color value.2).map Draw.clear
  else if value.1 = 1 then
    (decode rectFields value.2).map fun data =>
      .rect data.1 data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2
  else if value.1 = 2 then
    (decode circleFields value.2).map fun data => .circle data.1 data.2.1 data.2.2
  else if value.1 = 3 then
    (decode lineFields value.2).map fun data => .line data.1 data.2.1 data.2.2.1 data.2.2.2
  else if value.1 = 4 then
    (decode polygonFields value.2).map fun data => .polygon data.1 data.2
  else if value.1 = 5 then
    (decode textFields value.2).map fun data => .text data.1 data.2.1 data.2.2.1 data.2.2.2
  else none

def draw : Codec Draw := checked envelope drawValue parseDraw
  (by intro value; cases value <;> simp [drawValue, parseDraw, decode_write])

def listenerMask : Codec ListenerMask :=
  adapt (pair boolean (pair boolean (pair boolean (pair boolean boolean))))
    (fun value => (value.click, value.text, value.touch, value.key, value.resize))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)
    (by intro raw value accepted; cases accepted; rfl)

def propertyValue : Property → UInt8 × List UInt8
  | .text value => (0, text.write value)
  | .hint value => (1, text.write value)
  | .foreground value => (2, color.write value)
  | .background value => (3, color.write value)
  | .width value => (4, dimension.write value)
  | .height value => (5, dimension.write value)
  | .padding value => (6, natural.write value)
  | .weight value => (7, natural.write value)
  | .textSize value => (8, natural.write value)
  | .enabled value => (9, boolean.write value)
  | .description value => (10, text.write value)
  | .alignment value => (11, alignment.write value)
  | .drawing value => (12, (list draw).write value)
  | .listeners value => (13, listenerMask.write value)

def parseProperty (value : UInt8 × List UInt8) : Option Property :=
  if value.1 = 0 then (decode text value.2).map Property.text
  else if value.1 = 1 then (decode text value.2).map Property.hint
  else if value.1 = 2 then (decode color value.2).map Property.foreground
  else if value.1 = 3 then (decode color value.2).map Property.background
  else if value.1 = 4 then (decode dimension value.2).map Property.width
  else if value.1 = 5 then (decode dimension value.2).map Property.height
  else if value.1 = 6 then (decode natural value.2).map Property.padding
  else if value.1 = 7 then (decode natural value.2).map Property.weight
  else if value.1 = 8 then (decode natural value.2).map Property.textSize
  else if value.1 = 9 then (decode boolean value.2).map Property.enabled
  else if value.1 = 10 then (decode text value.2).map Property.description
  else if value.1 = 11 then (decode alignment value.2).map Property.alignment
  else if value.1 = 12 then (decode (list draw) value.2).map Property.drawing
  else if value.1 = 13 then (decode listenerMask value.2).map Property.listeners
  else none

def property : Codec Property := checked envelope propertyValue parseProperty
  (by intro value; cases value <;> simp [propertyValue, parseProperty, decode_write])

def patchValue : Patch → UInt8 × List UInt8
  | .create id kind => (0, (pair natural nodeKind).write (id, kind))
  | .property id value => (1, (pair natural property).write (id, value))
  | .insert parent index child =>
    (2, (pair natural (pair natural natural)).write (parent, index, child))
  | .remove id => (3, natural.write id)
  | .root id => (4, (optional natural).write id)

def parsePatch (value : UInt8 × List UInt8) : Option Patch :=
  if value.1 = 0 then
    (decode (pair natural nodeKind) value.2).map fun data => .create data.1 data.2
  else if value.1 = 1 then
    (decode (pair natural property) value.2).map fun data => .property data.1 data.2
  else if value.1 = 2 then
    (decode (pair natural (pair natural natural)) value.2).map fun data =>
      .insert data.1 data.2.1 data.2.2
  else if value.1 = 3 then (decode natural value.2).map Patch.remove
  else if value.1 = 4 then (decode (optional natural) value.2).map Patch.root
  else none

def patch : Codec Patch := checked envelope patchValue parsePatch
  (by intro value; cases value <;> simp [patchValue, parsePatch, decode_write])

end Kotlean.Wire
