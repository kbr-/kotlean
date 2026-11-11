module
public import Kotlean.Wire.Input
public import Kotlean.Wire.Option

@[expose] public section

namespace Kotlean.Wire

def bytes : Codec (List UInt8) := list byte

def sourceValue : Source → UInt8 × List UInt8
  | .tick ms => (0, natural.write ms)
  | .back => (1, []) | .pause => (2, []) | .resume => (3, [])
  | .platform name value => (4, (pair text bytes).write (name, value))

def parseSource (value : UInt8 × List UInt8) : Option Source :=
  if value.1 = 0 then (decode natural value.2).map Source.tick
  else if value.1 = 1 then some .back else if value.1 = 2 then some .pause
  else if value.1 = 3 then some .resume
  else if value.1 = 4 then
    (decode (pair text bytes) value.2).map fun data => .platform data.1 data.2
  else none

def source : Codec Source := checked envelope sourceValue parseSource
  (by intro value; cases value <;> simp [sourceValue, parseSource, decode_write])

def replyValue : Reply → UInt8 × List UInt8
  | .ok value => (0, bytes.write value)
  | .error value => (1, text.write value)

def parseReply (value : UInt8 × List UInt8) : Option Reply :=
  if value.1 = 0 then (decode bytes value.2).map Reply.ok
  else if value.1 = 1 then (decode text value.2).map Reply.error else none

def reply : Codec Reply := checked envelope replyValue parseReply
  (by intro value; cases value <;> simp [replyValue, parseReply, decode_write])

def eventValue : Event → UInt8 × List UInt8
  | .node revision id value =>
    (0, (pair natural (pair natural input)).write (revision, id, value))
  | .answer id value => (1, (pair natural reply).write (id, value))
  | .subscription generation id value =>
    (2, (pair natural (pair natural bytes)).write (generation, id, value))
  | .lifecycle active => (3, boolean.write active)
  | .save => (4, [])

def parseEvent (value : UInt8 × List UInt8) : Option Event :=
  if value.1 = 0 then
    (decode (pair natural (pair natural input)) value.2).map fun data =>
      .node data.1 data.2.1 data.2.2
  else if value.1 = 1 then
    (decode (pair natural reply) value.2).map fun data => .answer data.1 data.2
  else if value.1 = 2 then
    (decode (pair natural (pair natural bytes)) value.2).map fun data =>
      .subscription data.1 data.2.1 data.2.2
  else if value.1 = 3 then (decode boolean value.2).map Event.lifecycle
  else if value.1 = 4 then some .save else none

def event : Codec Event := checked envelope eventValue parseEvent
  (by intro value; cases value <;> simp [eventValue, parseEvent, decode_write])

def effectValue : Effect → UInt8 × List UInt8
  | .delay ms => (0, natural.write ms)
  | .read key => (1, text.write key)
  | .write key value => (2, (pair text bytes).write (key, value))
  | .log value => (3, text.write value)
  | .haptic => (4, [])
  | .clipboard value => (5, text.write value)
  | .platform name value => (6, (pair text bytes).write (name, value))

def parseEffect (value : UInt8 × List UInt8) : Option Effect :=
  if value.1 = 0 then (decode natural value.2).map Effect.delay
  else if value.1 = 1 then (decode text value.2).map Effect.read
  else if value.1 = 2 then
    (decode (pair text bytes) value.2).map fun data => .write data.1 data.2
  else if value.1 = 3 then (decode text value.2).map Effect.log
  else if value.1 = 4 then some .haptic
  else if value.1 = 5 then (decode text value.2).map Effect.clipboard
  else if value.1 = 6 then
    (decode (pair text bytes) value.2).map fun data => .platform data.1 data.2
  else none

def effect : Codec Effect := checked envelope effectValue parseEffect
  (by intro value; cases value <;> simp [effectValue, parseEffect, decode_write])

def command : Codec Command := adapt (pair natural effect)
  (fun value => (value.id, value.effect)) (fun value => some ⟨value.1, value.2⟩)
  (by intro value; cases value; rfl)
  (by intro raw value accepted; cases accepted; rfl)

def subscription : Codec Subscription := adapt (pair natural (pair natural source))
  (fun value => (value.id, value.generation, value.source))
  (fun value => some ⟨value.1, value.2.1, value.2.2⟩)
  (by intro value; cases value; rfl)
  (by intro raw value accepted; cases accepted; rfl)

end Kotlean.Wire
