module

public import PottsContinuity.BD12.TerminalHybridIndependence
public import PottsContinuity.BD12.BoundedVarianceDistance
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! DRT's variance-to-hybrid-increment reduction on the actual common seed
space. Independence and the zero-cutoff observable equality are proved in the
imported modules; neither is a premise of the reduction. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Integrals against the actual pinned law are the existing normalized mean. -/
theorem finitePinnedLaw_integral (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (g : Finset E → ℝ) :
    (∫ A, g A ∂(finitePinnedLaw w R H).toMeasure) = finitePinnedMean w R H g := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  exact (finitePinnedMean_eq_sum_law w R H g).symm

/-- Variance is bounded by half the expected sum of the actual stopped-hybrid
increments. No FKG premise is needed at this stage; it enters the subsequent
covariance estimate. Empty edge sets and observables independent of the state are included. -/
theorem finite_hybrid_variance_telescoping
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (fixedU : ℕ → ℝ) (background : ℕ → ℝ × ℝ) (T : FiniteRevealTree E ∅) :
    let seedLaw := finiteHybridSeedWindow 0 fixedU background 0 (Fintype.card E)
    let Y := fun t S => finiteJointHybridEval w f t
      (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false
    finitePinnedMean w ∅ ∅ (fun A => f A ^ 2) - (finitePinnedMean w ∅ ∅ f) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ t ∈ Finset.range (Fintype.card E),
        ∫ S, |f (Y (t + 1) S) - f (Y t S)| ∂seedLaw := by
  let seedLaw := finiteHybridSeedWindow 0 fixedU background 0 (Fintype.card E)
  let μ := (finitePinnedLaw w ∅ ∅).toMeasure
  let X := fun S : ℕ → ℝ × ℝ => finiteOriginalEval w (fun i => (S i).1) T ∅
  let Y := fun t (S : ℕ → ℝ × ℝ) => finiteJointHybridEval w f t
    (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false
  have hf : Measurable f := measurable_of_finite f
  have hY : ∀ t, Measurable (Y t) := fun t =>
    (finiteJointHybridEval_measurable w f t T ∅ ∅ false).comp
      (show Measurable (fun S : ℕ → ℝ × ℝ =>
        ((fun i => (S i).1), (fun i => (S i).2))) by fun_prop)
  have hX : Measurable X := (finiteOriginalEval_measurable w T ∅).comp
    (show Measurable (fun S : ℕ → ℝ × ℝ => fun i => (S i).1) by fun_prop)
  have hcost : ∀ s t, Integrable (fun S => |f (Y s S) - f (Y t S)|) seedLaw := fun s t =>
    integrable_of_unit_bounds seedLaw
      (continuous_abs.measurable.comp ((hf.comp (hY s)).sub (hf.comp (hY t))))
      (fun S => unit_interval_abs_sub _ _ (hf01 _) (hf01 _))
  have hzero : ∀ S, f (Y 0 S) = f (X S) := fun S =>
    finiteJointHybridEval_zero_observable w f _ _ T ∅
  have hterminal : seedLaw.map (fun S => (X S, Y (Fintype.card E) S)) = μ.prod μ :=
    finiteHybridFamilyEval_terminal_product w f fixedU (fun _ : Unit => Fintype.card E)
      background T () le_rfl
  have hdist : (∫ AB, |f AB.1 - f AB.2| ∂μ.prod μ) =
      ∫ S, |f (Y 0 S) - f (Y (Fintype.card E) S)| ∂seedLaw := by
    rw [← hterminal, integral_map_of_stronglyMeasurable (hX.prodMk (hY _))
      (measurable_of_finite (fun AB : Finset E × Finset E => |f AB.1 - f AB.2|)).stronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun S => by
      change |f (X S) - f (Y (Fintype.card E) S)| =
        |f (Y 0 S) - f (Y (Fintype.card E) S)|
      rw [hzero S])
  have hfirst : finitePinnedMean w ∅ ∅ (fun A => f A ^ 2) - (finitePinnedMean w ∅ ∅ f) ^ 2 ≤
      (1 / 2 : ℝ) * ∫ S, |f (Y 0 S) - f (Y (Fintype.card E) S)| ∂seedLaw := by
    have h := bounded_variance_le_independent_distance μ f hf hf01
    rw [finitePinnedLaw_integral, finitePinnedLaw_integral, hdist] at h
    exact h
  have hsum : Integrable (fun S => ∑ t ∈ Finset.range (Fintype.card E),
      |f (Y (t + 1) S) - f (Y t S)|) seedLaw :=
    integrable_finsetSum _ (fun t _ => hcost (t + 1) t)
  have htele := integral_mono (f := fun S => |f (Y 0 S) - f (Y (Fintype.card E) S)|)
    (g := fun S => ∑ t ∈ Finset.range (Fintype.card E), |f (Y (t + 1) S) - f (Y t S)|)
    (hcost 0 _) hsum (fun S => abs_sub_le_sum_adjacent (fun t => f (Y t S)) (Fintype.card E))
  rw [integral_finsetSum _ (fun t _ => hcost (t + 1) t)] at htele
  exact hfirst.trans (mul_le_mul_of_nonneg_left htele (by norm_num))

end
end PottsContinuity.BD12
