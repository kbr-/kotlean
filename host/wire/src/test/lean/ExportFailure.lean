module
import Kotlean
meta import Kotlean.Export

initialize do throw (IO.userError "Kotlean intentional initialization failure")

def app : Kotlean.App := {
  Model := Unit
  Msg := Unit
  init := ((), [])
  update := fun _ _ => ((), [])
  view := fun _ => .empty
}

kotlean_app app
