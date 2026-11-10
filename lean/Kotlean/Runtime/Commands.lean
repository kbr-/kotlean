module
public import Kotlean.Runtime.State

@[expose] public section

namespace Kotlean.Runtime.RequestState

def empty : RequestState Msg := ⟨0, ∅, by intro id present; simp at present⟩

def issue (state : RequestState Msg) (command : Cmd Msg) : RequestState Msg × Command :=
  let result := Runtime.issue state.next state.pending command
  (⟨result.2.1, result.2.2, Runtime.issue_bounded state.next state.pending command state.bounded⟩,
    result.1)

theorem issue_agrees (state : RequestState Msg) (command : Cmd Msg) :
    Runtime.issue state.next state.pending command =
      ((issue state command).2, (issue state command).1.next, (issue state command).1.pending) := rfl

def take (state : RequestState Msg) (id : Nat) :
    Option (Reply → Option Msg) × RequestState Msg :=
  let result := Runtime.consume id state.pending
  (result.1, ⟨state.next, result.2, Runtime.consume_bounded state.next state.pending id state.bounded⟩)

def batchAux (state : RequestState Msg) (commands : List (Cmd Msg))
    (reverseOutput : List Command) : RequestState Msg × List Command :=
  match commands with
  | [] => (state, reverseOutput.reverse)
  | command :: commands =>
    let result := issue state command
    batchAux result.1 commands (result.2 :: reverseOutput)

def batch (state : RequestState Msg) (commands : List (Cmd Msg)) :
    RequestState Msg × List Command := batchAux state commands []

theorem batchAux_run (state : RequestState Msg) (commands : List (Cmd Msg))
    (reverseOutput : List Command) :
    ∃ emitted, CommandRun state commands (batchAux state commands reverseOutput).1 emitted ∧
      (batchAux state commands reverseOutput).2 = reverseOutput.reverse ++ emitted := by
  induction commands generalizing state reverseOutput with
  | nil => exact ⟨[], .nil state, by simp [batchAux]⟩
  | cons command commands ih =>
    obtain ⟨emitted, run, output⟩ := ih (issue state command).1
      ((issue state command).2 :: reverseOutput)
    refine ⟨(issue state command).2 :: emitted, .cons (issue_agrees state command) run, ?_⟩
    simpa only [batchAux, List.reverse_cons, List.append_assoc, List.singleton_append] using output

theorem batch_run (state : RequestState Msg) (commands : List (Cmd Msg)) :
    CommandRun state commands (batch state commands).1 (batch state commands).2 := by
  obtain ⟨emitted, run, output⟩ := batchAux_run state commands []
  simp only [List.reverse_nil, List.nil_append] at output
  simpa only [batch, output] using run

theorem batch_nil (state : RequestState Msg) : batch state [] = (state, []) := rfl

end Kotlean.Runtime.RequestState

namespace Kotlean.Runtime.CommandRun

theorem effects {initial final : RequestState Msg} {commands : List (Cmd Msg)} {output : List Command}
    (run : CommandRun initial commands final output) :
    output.map Command.effect = commands.map Cmd.effect := by
  induction run with
  | nil => rfl
  | @cons initial advanced final command output commands outputs issued rest ih =>
    have selected := congrArg (fun result => result.1.effect) issued
    have effect := (Runtime.issue_selected initial.next initial.pending command).2.1
    simp only [List.map_cons]
    rw [selected.symm.trans effect, ih]

theorem next {initial final : RequestState Msg} {commands : List (Cmd Msg)} {output : List Command}
    (run : CommandRun initial commands final output) : final.next = initial.next + commands.length := by
  induction run with
  | nil => simp
  | @cons initial advanced final command output commands outputs issued rest ih =>
    have selected := congrArg (fun result => result.2.1) issued
    have increased := (Runtime.issue_selected initial.next initial.pending command).2.2.1
    have advancedNext : advanced.next = initial.next + 1 := selected.symm.trans increased
    simp only [List.length_cons]
    rw [ih, advancedNext]
    omega

theorem older {initial final : RequestState Msg} {commands : List (Cmd Msg)} {output : List Command}
    (run : CommandRun initial commands final output) (id : Nat) (bound : id < initial.next) :
    final.pending[id]? = initial.pending[id]? := by
  induction run with
  | nil => rfl
  | @cons initial advanced final command output commands outputs issued rest ih =>
    have selected := Runtime.issue_selected initial.next initial.pending command
    have advancedNext : advanced.next = initial.next + 1 := by
      have h := congrArg (fun result => result.2.1) issued
      exact h.symm.trans selected.2.2.1
    have advancedPending : advanced.pending[id]? = initial.pending[id]? := by
      have h := congrArg (fun result => result.2.2[id]?) issued
      exact h.symm.trans (selected.2.2.2.2 id (by omega))
    exact (ih (by omega)).trans advancedPending

end Kotlean.Runtime.CommandRun
