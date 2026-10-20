module

public import PottsContinuity.Thm3.Prop4.TubeConfinedExponentialBound
public import PottsContinuity.Thm3.Prop4.OneArmRatio

/-!
# The actual tube probability has the squared-arm term of Lemma 7

Adjacent-radius insertion converts the n,n-1 product without any radius
loss. The prefactor is uniform over the endpoint pair and scale.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual tube-confined finite connection is bounded by a uniform
factor times the squared infinite arm with the fractional-exponential loss. -/
theorem widened_tube_connection_squared_arm_bound_of_touch
    (q : Set.Ici (1 : ℝ)) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a b : (box n : Set LatticeVertex),
      a.val.1 = -(n : ℤ) → b.val.1 = n →
      (measure (squareLattice.induce (box n : Set LatticeVertex)) (RSW.selfDualParameters q)
        (BoundaryCondition.free ∅) {A | ∃ p : (openGraph _ A).Walk a b,
          ∀ z ∈ p.support, z.val ∈ radiusTube n (4*(n : ℝ)^ε) a.val b.val}).toReal ≤
        A*Real.exp (C*(n : ℝ)^ε)*(RSW.oneArmProbability μ n)^2 := by
  obtain ⟨C,hC,hbound⟩ := widened_tube_connection_exponential_bound_of_touch q ε hε μ hμ hTouch
  obtain ⟨D,hD,hratio⟩ := oneArm_probability_upper_ratio (RSW.selfDualParameters q) μ hμ
  refine ⟨D,C,lt_of_lt_of_le zero_lt_one hD,hC,?_⟩
  intro n hn a b ha hb
  have hstep := hratio (n-1)
  rw [Nat.sub_add_cancel hn] at hstep
  apply (hbound n hn a b ha hb).trans
  calc
    _ ≤ Real.exp (C*(n : ℝ)^ε)*RSW.oneArmProbability μ n*
        (D*RSW.oneArmProbability μ n) :=
      mul_le_mul_of_nonneg_left hstep (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    _ = _ := by ring

end
end PottsContinuity.Thm3.Prop4
