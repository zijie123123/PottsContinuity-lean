module

public import PottsContinuity.Thm3.Prop4.TubeConnectionTouchBound
public import PottsContinuity.Thm3.Prop4.WidenedTouchPenalty

/-!
# Exponential comparison for the actual tube-confined connection

The cost is uniform over opposite-side endpoints and every positive scale.
It combines both closing costs and the actual squared touch factor.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual free finite-box connection confined to the widened tube has
the n,n-1 infinite arm-product bound with a uniform exponential prefactor. -/
theorem widened_tube_connection_exponential_bound_of_touch
    (q : Set.Ici (1 : ℝ)) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a b : (box n : Set LatticeVertex),
      a.val.1 = -(n : ℤ) → b.val.1 = n →
      (measure (squareLattice.induce (box n : Set LatticeVertex)) (RSW.selfDualParameters q)
        (BoundaryCondition.free ∅) {A | ∃ p : (openGraph _ A).Walk a b,
          ∀ z ∈ p.support, z.val ∈ radiusTube n (4*(n : ℝ)^ε) a.val b.val}).toReal ≤
        Real.exp (C*(n : ℝ)^ε) * RSW.oneArmProbability μ n * RSW.oneArmProbability μ (n-1) := by
  let D := Real.log 25920+4/ε
  let C := 8*tubeClosingCoefficient (RSW.selfDualParameters q)+2*D
  have hD : 0 < D := add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num))
    (div_pos (by norm_num) hε)
  have hcoeff := tubeClosingCoefficient_pos (RSW.selfDualParameters q)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n hn a b ha hb
  have hr : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
  have hbase := tube_connection_arm_product_lower_of_touch q hn (4*(n : ℝ)^ε)
    (by linarith only [hr]) a b ha hb μ hμ hTouch
  have hp := widened_touch_denominator_exponential_lower ε hε hn
  have hsq := mul_le_mul hp hp (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hp)
  have heq : Real.exp (-C*(n : ℝ)^ε) =
      Real.exp (-(2*tubeClosingCoefficient (RSW.selfDualParameters q))*(4*(n : ℝ)^ε)) *
        (Real.exp (-D*(n : ℝ)^ε)*Real.exp (-D*(n : ℝ)^ε)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp [C]
    ring
  have hpen : Real.exp (-C*(n : ℝ)^ε) ≤
      Real.exp (-(2*tubeClosingCoefficient (RSW.selfDualParameters q))*(4*(n : ℝ)^ε)) *
        (1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2))^2 := by
    rw [heq,pow_two]
    exact mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
  have hbound := (mul_le_mul_of_nonneg_right hpen ENNReal.toReal_nonneg).trans hbase
  have hinv : (Real.exp (-C*(n : ℝ)^ε))⁻¹ = Real.exp (C*(n : ℝ)^ε) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hdivide := (le_div_iff₀' (Real.exp_pos (-C*(n : ℝ)^ε))).mpr hbound
  rw [div_eq_mul_inv,hinv] at hdivide
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hdivide

end
end PottsContinuity.Thm3.Prop4
