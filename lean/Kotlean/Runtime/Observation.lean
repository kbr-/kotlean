module
public import Kotlean.Runtime.State

@[expose] public section

namespace Kotlean.Runtime

def edited (scene : View.Scene) (id : Nat) (text : String) : View.Scene :=
  { scene with nodes := scene.nodes.map (fun key node =>
      if key == id then { node with properties := { node.properties with text := text } } else node) }

def isTextEdit (scene : View.Scene) (id : Nat) : Input → Bool
  | .text _ => (scene.nodes[id]?).any (fun node => node.kind == .input)
  | _ => false

def observed (scene : View.Scene) (revision : Nat) : Event → View.Scene
  | .node received id (.text text) =>
    if received == revision && (scene.nodes[id]?).any (fun node => node.kind == .input)
    then edited scene id text else scene
  | _ => scene

end Kotlean.Runtime
