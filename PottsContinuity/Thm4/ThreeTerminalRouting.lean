/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ThreeTerminalRouting.lean`.
Adaptation: namespace relocation only.
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4.Medial

abbrev ThreeTerminal := Fin 3

def threeTerminalSwap : Equiv.Perm ThreeTerminal := Equiv.swap 1 2

def openRoutingSuccessor (p : Equiv.Perm ThreeTerminal) : Equiv.Perm ThreeTerminal :=
  p.trans threeTerminalSwap

def firstPositiveReturnLength (p : Equiv.Perm ThreeTerminal) : ℕ :=
  if p 0 = 0 then 1 else if p (p 0) = 0 then 2 else 3

theorem firstPositiveReturnLength_returns (p : Equiv.Perm ThreeTerminal) :
    (p^[firstPositiveReturnLength p]) 0 = 0 := by
  fin_cases p <;> decide

theorem threeTerminalSwap_zero : threeTerminalSwap 0 = 0 := by
  simp [threeTerminalSwap, Equiv.swap_apply_def]

theorem threeTerminalSwap_one : threeTerminalSwap 1 = 2 := by
  simp [threeTerminalSwap]

theorem threeTerminalSwap_two : threeTerminalSwap 2 = 1 := by
  simp [threeTerminalSwap]

theorem openRoutingSuccessor_apply (p : Equiv.Perm ThreeTerminal)
    (x : ThreeTerminal) : openRoutingSuccessor p x = threeTerminalSwap (p x) := by
  rfl

end PottsContinuity.Thm4.Medial
