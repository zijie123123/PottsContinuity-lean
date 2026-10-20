module

public import PottsContinuity.BD12.DRTMeanOrder

/-! Strict upper bounds for actual finite expectations from a configuration
of strictly positive weight on which the observable is below one. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance strictMeanEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- A genuine failure configuration makes the mean strictly smaller than one. -/
theorem drtMean_lt_one_of_exists_failure (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ)
    (hf : ∀ A, f A ≤ 1) (hfail : ∃ A, f A < 1) : drtMean G q ξ J β f < 1 := by
  unfold drtMean
  apply (div_lt_one (drtPartition_pos G q ξ J β)).mpr
  obtain ⟨A, hA⟩ := hfail
  apply Finset.sum_lt_sum
  · intro C _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf C) (drtWeight_pos G q ξ J β C).le
  · refine ⟨A, Finset.mem_univ _, ?_⟩
    simpa only [mul_one] using mul_lt_mul_of_pos_left hA (drtWeight_pos G q ξ J β A)

end
end PottsContinuity.BD12
