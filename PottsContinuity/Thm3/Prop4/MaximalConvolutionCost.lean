module

public import PottsContinuity.Thm3.Prop4.MaximalTouchCost

/-!
# The final n^4 coefficient and exact convolution cutoff

The genuine source-record inequality loses only a parameter-only coefficient.
Both convolution radii shift by one, preserving the real lower cutoff.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK

/-- Every full real-cutoff convolution is nonnegative for nonnegative arms. -/
theorem splitArmSum_nonneg (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (r : ℝ) (N : ℕ) :
    0 ≤ splitArmSum a r N := by
  classical
  unfold splitArmSum
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (ha k) (ha (N-k))
  · exact le_rfl

/-- One common positive coefficient removes the actual touch/star penalty
and changes total radius 2n-2 to 2n, uniformly over all cutoffs and n. -/
theorem exists_maximal_split_coefficient (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r S : ℝ,
      (1-edgeParameter θ)^4 *
        (1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2))*S ≤
        splitArmSum (RSW.oneArmProbability μ) r (2*n-2) →
      S ≤ C*(n : ℝ)^4*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  obtain ⟨D,hD,hshift⟩ := oneArm_split_sum_shift θ μ hμ
  let C := (81920/(1-edgeParameter θ)^4)*D^2
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hc : 0 < (1-edgeParameter θ)^4 := pow_pos (one_sub_edgeParameter_pos θ) _
  refine ⟨C,mul_pos (div_pos (by norm_num) hc) (sq_pos_of_pos hDpos),?_⟩
  intro n hn r S h
  have hExtract := maximal_touch_star_cost_extract θ hn S
    (splitArmSum (RSW.oneArmProbability μ) r (2*n-2))
    (splitArmSum_nonneg _ (fun _ => ENNReal.toReal_nonneg) _ _) h
  calc
    _ ≤ (81920/(1-edgeParameter θ)^4)*(n : ℝ)^4*
        splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := hExtract
    _ ≤ (81920/(1-edgeParameter θ)^4)*(n : ℝ)^4*
        (D^2*splitArmSum (RSW.oneArmProbability μ) r (2*n)) :=
      mul_le_mul_of_nonneg_left (hshift r n hn) (by positivity)
    _ = _ := by dsimp [C]; ring

end PottsContinuity.Thm3.Prop4
