module

public import PottsContinuity.BD12.BoxRadiusRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Literal finite one-arm events on arbitrary induced lattice domains. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- Original open connectivity from o to the exact coordinate radius n about c. -/
def finiteDomainOneArmEvent (S : Finset LatticeVertex) (c : LatticeVertex)
    (o : (S : Set LatticeVertex)) (n : ℕ) : Set (Configuration (finiteLatticeGraph S)) :=
  {A | ∃ b : (S : Set LatticeVertex), latticeRadius c b.val = n ∧
    FKC.FiniteFK.ActualConnected (finiteLatticeGraph S) A o b}

theorem finiteDomainOneArmEvent_isUpperSet (S : Finset LatticeVertex) (c : LatticeVertex)
    (o : (S : Set LatticeVertex)) (n : ℕ) : IsUpperSet (finiteDomainOneArmEvent S c o n) := by
  intro A D hAD hA
  obtain ⟨b, hb, hconn⟩ := hA
  exact ⟨b, hb, FKC.FiniteFK.actualConnected_mono hAD hconn⟩

/-- The event indicator is exactly the existing radius one-arm observable. -/
theorem finiteDomainOneArmEvent_indicator (S : Finset LatticeVertex) (c : LatticeVertex)
    (o : (S : Set LatticeVertex)) (n : ℕ) :
    (finiteDomainOneArmEvent S c o n).indicator (fun _ => (1 : ℝ)) =
      radiusOneArmIndicator (finiteLatticeGraph S) (fun v => latticeRadius c v.val) o n := by
  funext A
  simp only [Set.indicator, finiteDomainOneArmEvent, Set.mem_ofPred_eq,
    radiusOneArmIndicator, finiteConnectionToSetIndicator, mem_finiteRadiusShell]
  congr

end
end PottsContinuity.BD12
