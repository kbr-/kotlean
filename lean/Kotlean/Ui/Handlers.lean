import Kotlean.Ui.Laws

namespace Kotlean.Handlers

def mask {Msg : Type} (handlers : Handlers Msg) : ListenerMask :=
  { click := handlers.click.isSome, text := handlers.text.isSome,
    touch := handlers.touch.isSome, key := handlers.key.isSome, resize := handlers.resize.isSome }

def dispatch {Msg : Type} (handlers : Handlers Msg) : Input → Option Msg
  | .click => handlers.click
  | .text text => handlers.text.map (fun f => f text)
  | .touch frame => handlers.touch.map (fun f => f frame)
  | .key code down => handlers.key.map (fun f => f code down)
  | .resize width height density => handlers.resize.map (fun f => f width height density)

theorem mask_correct {Msg : Type} : Ui.Laws.maskContract (@mask Msg) := by
  intro handlers
  rfl

theorem dispatch_correct {Msg : Type} : Ui.Laws.dispatchContract (@dispatch Msg) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end Kotlean.Handlers

namespace Kotlean.Attributes

def renderProperties {Msg : Type} (attributes : Attributes Msg) : Properties :=
  { attributes.toProperties with listeners := attributes.events.mask }

theorem renderProperties_correct {Msg : Type} :
    Ui.Laws.propertiesContract (@Handlers.mask Msg) (@renderProperties Msg) := by
  intro attributes
  rfl

end Kotlean.Attributes
