module
import Kotlean
meta import Kotlean.Export

def app : Kotlean.App := {
  Model := String
  Msg := String
  init := ("ready", [])
  update := fun value _ => (value, [])
  view := fun value => .input { text := value, events := { text := some id } }
  persistence := some ⟨Kotlean.Wire.text.write, Kotlean.Wire.decode Kotlean.Wire.text⟩
}

kotlean_app app
