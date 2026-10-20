module

public import PottsContinuity.Thm3.Push.SquareDualReflectionVertices
public import PottsContinuity.Thm3.Push.IntervalArmDualPorts

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Complementing actual original states commutes with the exact finite
primal/dual reflection, without any boundary-law premise. -/
theorem squareDualReflection_closed_configuration (N : ℕ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    configurationIso (squareDualReflectionIso N)
      (auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv (0,0) N N) A) =
    auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
      (configurationIso (squareArmReflectionIso N) A) := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv (0,0) N N
  let P := configurationIsoEdgeEquiv (squareArmReflectionIso N)
  let D := configurationIsoEdgeEquiv (squareDualReflectionIso N)
  ext d
  obtain ⟨c,rfl⟩ := D.surjective d
  obtain ⟨f,rfl⟩ := e.surjective c
  have hl : D (e f) ∈ configurationIso (squareDualReflectionIso N) (auxiliaryClosedConfiguration e A) ↔ f ∉ A := by
    change D (e f) ∈ (auxiliaryClosedConfiguration e A).map D.toEmbedding ↔ _
    rw [Finset.mem_map_equiv]
    simpa only [Equiv.symm_apply_apply] using mem_auxiliaryClosedConfiguration e A (e f)
  have hr : D (e f) ∈ auxiliaryClosedConfiguration e (configurationIso (squareArmReflectionIso N) A) ↔ f ∉ A := by
    have hpair : D (e f) = e (P f) := squareDualReflection_edge_commutes N f
    rw [hpair,mem_auxiliaryClosedConfiguration,e.symm_apply_apply]
    change (P f ∉ A.map P.toEmbedding) ↔ f ∉ A
    simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
  exact hl.trans hr.symm

/-- Exact image of the left and bottom-left ports is the right and
bottom-right ports, with no one-unit endpoint discrepancy. -/
theorem squareDualReflection_left_ports_map (N : ℕ) (r : ℤ) :
    (intervalArmLeftDualPorts N ((N:ℤ)-r)).map (squareDualReflectionIso N).toEquiv.toEmbedding =
      intervalArmRightDualPorts N r := by
  classical
  ext v
  rw [Finset.mem_map_equiv,mem_intervalArmLeftDualPorts,mem_intervalArmRightDualPorts]
  change (((N:ℤ)-v.val.1-1 = -1) ∨
    (v.val.2 = -1 ∧ (N:ℤ)-v.val.1-1 < (N:ℤ)-r)) ↔
    (v.val.1=(N:ℤ) ∨ (v.val.2 = -1 ∧ r ≤ v.val.1))
  omega

end
end PottsContinuity.Push
