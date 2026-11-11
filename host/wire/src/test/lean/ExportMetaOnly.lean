module
import Kotlean
meta import ExportNat
meta import Kotlean.Export

def fixture : Kotlean.App := {
  Model := Unit
  Msg := Unit
  init := ((), [])
  update := fun _ model => (model, [])
  view := fun _ => .column {}
    [ .text { text := "Runtime app", width := .dp 2147483648 }
    , .canvas {
        width := .dp 32
        height := .dp 32
        description := "Clear probe"
        drawing := [.rect ⟨0, 0⟩ 50000 50000 0 0xffff0000, .clear 0] } ]
}

kotlean_app fixture
