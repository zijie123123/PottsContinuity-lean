module

public import PottsContinuity.BD12.DRTInverseTemperature
public import PottsContinuity.BD12.DRTWiredInfiniteArmBound
public import PottsContinuity.BD12.SquareOneArmBound

/-! Polynomial lower bound for the actual finite source one-arm sequence
at the explicit self-dual parameter, every real q>=1. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- The square bound rules out exponential decay of the finite source sequence
at the explicit self-dual parameter. No genuine threshold equality is assumed. -/
theorem selfDual_source_one_arm_polynomial_lower_bound (q : Set.Ici (1 : ℝ)) (n : ℕ) :
    (1/2 : ℝ) ≤ (n+1 : ℕ) * drtWiredOneArmMean
      ⟨(q : ℝ), (show (0 : ℝ) < (q : ℝ) from lt_of_lt_of_le one_pos q.property)⟩
      (drtInverseTemperature (criticalParameters q)) n := by
  let θ := criticalParameters q
  obtain ⟨μ,hμ⟩ := Foundations.exists_isRCInfiniteVolumeLimit θ.toP θ.toQ θ.property 1
  have hμ' : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters ⟨θ.val,clusterWeight_pos θ⟩ θ.property (drtInverseTemperature θ)).toP
      (drtHomogeneousParameters ⟨θ.val,clusterWeight_pos θ⟩ θ.property (drtInverseTemperature θ)).toQ 1 μ := by
    rw [drtHomogeneousParameters_inverse]
    exact hμ
  have hupper := drt_wired_infinite_radius_le_one_arm_mean ⟨θ.val,clusterWeight_pos θ⟩ θ.property
    (drtInverseTemperature θ) μ hμ' n
  exact (wired_selfDual_one_arm_polynomial_lower_bound q μ hμ n).trans
    (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg (n+1)))

end
end PottsContinuity.BD12
