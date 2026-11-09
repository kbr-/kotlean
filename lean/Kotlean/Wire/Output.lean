import Kotlean.Wire.Effects
import Kotlean.Wire.Drawing

namespace Kotlean.Wire

private def changeValue : SubscriptionChange → UInt8 × List UInt8
  | .add value => (0, subscription.write value)
  | .remove id generation => (1, (pair natural natural).write (id, generation))

private def parseChange (value : UInt8 × List UInt8) : Option SubscriptionChange :=
  if value.1 = 0 then (decode subscription value.2).map SubscriptionChange.add
  else if value.1 = 1 then
    (decode (pair natural natural) value.2).map fun data => .remove data.1 data.2
  else none

def subscriptionChange : Codec SubscriptionChange := checked envelope changeValue parseChange
  (by intro value; cases value <;> simp [changeValue, parseChange, decode_write])

def output : Codec Output :=
  adapt (pair natural (pair (list patch) (pair (list command)
    (pair (list subscriptionChange) (optional bytes)))))
    (fun value => (value.revision, value.patches, value.commands, value.subscriptions, value.snapshot))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)
    (by intro raw value accepted; cases accepted; rfl)

private def outValue : Out → UInt8 × List UInt8
  | .changes value => (0, output.write value)
  | .ignored value => (1, (optional text).write value)
  | .failed value => (2, text.write value)

private def parseOut (value : UInt8 × List UInt8) : Option Out :=
  if value.1 = 0 then (decode output value.2).map Out.changes
  else if value.1 = 1 then (decode (optional text) value.2).map Out.ignored
  else if value.1 = 2 then (decode text value.2).map Out.failed else none

def out : Codec Out := checked envelope outValue parseOut
  (by intro value; cases value <;> simp [outValue, parseOut, decode_write])

def initInput : Codec InitInput := adapt (optional bytes)
  (fun value => value.snapshot) (fun value => some ⟨value⟩)
  (by intro value; cases value; rfl)
  (by intro raw value accepted; cases accepted; rfl)

end Kotlean.Wire
