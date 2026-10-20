module

public import PottsContinuity.Thm3.Prop4.SideArmExtension
public import PottsContinuity.PD.RCInfinite.MeasurableBounds

/-!
# A uniform adjacent-radius bound for the frozen free one-arm probability

The proof uses four whole-face events, translation invariance and one original
edge insertion per face. It introduces no radius-dependent loss.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Adjacent radii retain a fixed positive fraction of the actual arm mass,
for all radii including zero and every independent interior parameter. -/
theorem oneArm_probability_adjacent_lower (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (n : ℕ) :
    (PD.RCInfinite.energyBound θ/4)*RSW.oneArmProbability μ n ≤
      RSW.oneArmProbability μ (n+1) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hcover : RSW.oneArmProbability μ n ≤ ∑ d : Fin 4, μ.real (sideArmEvent n d) :=
    (measureReal_mono (infiniteArmEvent_subset_sideArms n)).trans
      (measureReal_iUnion_fintype_le (sideArmEvent n))
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (d : Fin 4) _ => sideArm_probability_extension θ μ hμ n d)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hscale := mul_le_mul_of_nonneg_left hcover (PD.RCInfinite.energyBound_pos θ).le
  norm_num at hsum
  nlinarith only [hscale,hsum]

/-- The actual adjacent-index upper ratio used by the numerical decay chain.
The bound is uniform in n and retains the frozen infinite-volume predicate. -/
theorem oneArm_probability_upper_ratio (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ n : ℕ,
      RSW.oneArmProbability μ n ≤ D*RSW.oneArmProbability μ (n+1) := by
  have he : 0 < PD.RCInfinite.energyBound θ := PD.RCInfinite.energyBound_pos θ
  have he1 : PD.RCInfinite.energyBound θ ≤ 1 :=
    (min_le_left _ _).trans (PD.RCInfinite.openEnergy_le_one θ)
  refine ⟨4/PD.RCInfinite.energyBound θ, (le_div_iff₀ he).mpr (by linarith), ?_⟩
  intro n
  have h := oneArm_probability_adjacent_lower θ μ hμ n
  have hd : RSW.oneArmProbability μ n ≤ RSW.oneArmProbability μ (n+1)/
      (PD.RCInfinite.energyBound θ/4) :=
    (le_div_iff₀ (div_pos he (by norm_num : (0 : ℝ) < 4))).mpr
      (by simpa only [mul_comm] using h)
  simpa only [div_div, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm, mul_assoc] using hd

end PottsContinuity.Thm3.Prop4
