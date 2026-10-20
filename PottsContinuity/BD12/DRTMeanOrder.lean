module

public import PottsContinuity.BD12.DRTFiniteLaw

/-! Order properties of expectations under the actual finite weighted FK law. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance meanOrderEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- A nonnegative actual finite observable has nonnegative mean. -/
theorem drtMean_nonneg (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f : Configuration G → ℝ) (hf : ∀ A, 0 ≤ f A) : 0 ≤ drtMean G q ξ J β f := by
  rw [drtMean_eq_sum_law]
  exact Finset.sum_nonneg (fun A _ => mul_nonneg ENNReal.toReal_nonneg (hf A))

/-- Pointwise order of actual observables passes to their weighted means. -/
theorem drtMean_mono (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f g : Configuration G → ℝ) (hfg : ∀ A, f A ≤ g A) :
    drtMean G q ξ J β f ≤ drtMean G q ξ J β g := by
  simp only [drtMean_eq_sum_law]
  exact Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (hfg A) ENNReal.toReal_nonneg)

end
end PottsContinuity.BD12
