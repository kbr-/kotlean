module
import Kotlean
meta import Kotlean.Export

def app : Kotlean.App := {
  Model := Nat
  Msg := Bool
  init := (7, [])
  update := fun increment count => (if increment then count + 1 else count - 1, [])
  view := fun count => .button { text := toString count, events := { click := some true } }
  persistence := some ⟨Kotlean.Wire.natural.write, Kotlean.Wire.decode Kotlean.Wire.natural⟩
}

kotlean_app app
