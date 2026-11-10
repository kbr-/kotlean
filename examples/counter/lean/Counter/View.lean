import Kotlean

namespace Counter

inductive Msg where
  | increment
  | decrement
  | addLater
  deriving Repr, DecidableEq

def view (count : Nat) : Kotlean.Ui Msg :=
  .column { width := .fill, padding := 20 }
    [ .text { text := "Kotlean counter", textSize := 20 },
      .text { text := toString count, textSize := 40, padding := 12 },
      .row { padding := 8 }
        [ .button { text := "−", events := { click := some .decrement } },
          .button { text := "+", events := { click := some .increment } },
          .button { text := "Add later", events := { click := some .addLater } } ] ]

theorem view_valid (count : Nat) : Kotlean.View.Canonical.valid (Kotlean.Ui.compile (view count)).scene :=
  Kotlean.Ui.compile_canonical _

theorem view_diff_correct (old new : Nat) :
    Kotlean.View.applyPatches
      (Kotlean.View.diffScene (Kotlean.Ui.compile (view old)).scene (Kotlean.Ui.compile (view new)).scene)
      (Kotlean.Ui.compile (view old)).scene = some (Kotlean.Ui.compile (view new)).scene :=
  Kotlean.Ui.compile_diff_correct _ _

end Counter
