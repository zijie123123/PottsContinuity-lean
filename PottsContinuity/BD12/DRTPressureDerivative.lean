module

public import PottsContinuity.BD12.DRTRusso
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The pressure derivative for the actual weighted FK partition function. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
open scoped BigOperators
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance pressureDerivativeEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- The logarithmic partition derivative is the sum of actual edge
intensities multiplied by the corrected DRT bond scores. -/
theorem drtLogPartition_hasDerivAt (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) :
    HasDerivAt (fun t : ℝ => Real.log (∑ A, drtWeight G q ξ J t A))
      (∑ e : G.edgeSet, drtEdgeScore G J β e *
        drtMean G q ξ J β (drtEdgeIndicator G e)) β := by
  have hZ : HasDerivAt (fun t : ℝ => ∑ A, drtWeight G q ξ J t A)
      (∑ A, drtWeight G q ξ J β A * ∑ e ∈ A, drtEdgeScore G J β e) β :=
    HasDerivAt.fun_sum (fun A _ => drtWeight_hasDerivAt G q ξ J β A)
  have hmean :
      (∑ A, drtWeight G q ξ J β A * ∑ e ∈ A, drtEdgeScore G J β e) /
          (∑ A, drtWeight G q ξ J β A) =
        ∑ e : G.edgeSet, drtEdgeScore G J β e *
          drtMean G q ξ J β (drtEdgeIndicator G e) := by
    change drtMean G q ξ J β (fun A => ∑ e ∈ A, drtEdgeScore G J β e) = _
    have hscore := funext (drtScore_eq_sum_indicators G J β)
    rw [hscore, drtMean_sum]
    simp_rw [drtMean_const_mul]
  simpa only [hmean] using hZ.log (drtPartition_pos G q ξ J β).ne'

/-- For homogeneous unit couplings the score is common to every edge. -/
theorem drtLogPartition_homogeneous_hasDerivAt (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (β : Set.Ioi (0 : ℝ)) :
    HasDerivAt (fun t : ℝ => Real.log (∑ A,
      drtWeight G q ξ (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) t A))
      ((Real.exp (β : ℝ) / (Real.exp (β : ℝ) - 1)) *
        ∑ e : G.edgeSet, drtMean G q ξ (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) β
          (drtEdgeIndicator G e)) β := by
  simpa only [drtEdgeScore, mul_one, one_mul, Finset.mul_sum] using
    drtLogPartition_hasDerivAt G q ξ (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) β

end
end PottsContinuity.BD12
