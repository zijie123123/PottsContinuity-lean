module

public import PottsContinuity.BD12.ActiveHybridCovariance
public import PottsContinuity.BD12.ActiveQueryRegularity
public import PottsContinuity.BD12.OriginalPinBlockSplit
public import PottsContinuity.BD12.OptionQueryIntegral
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Average the selected-query covariance estimate over the actual original
prefix. The right side is weighted by the measurable active-edge fibres. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]
    [MeasurableSpace (Option E)] [MeasurableSingletonClass (Option E)]

/-- The actual unconditional hybrid increment at time t is bounded by the sum
of twice the edge covariance weighted by its active-query probability. These
probabilities use the actual t-dimensional original prefix, with no supplied
revealment estimate or stopping event. -/
theorem finiteActiveHybrid_switch_cost_average_le
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (ht : t ≤ Fintype.card E) (T : FiniteRevealTree E ∅) :
    (∫ W, ∫ v,
      |f (finiteJointHybridEval w f (t + 1) W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) -
        f (finiteJointHybridEval w f t W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)|
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
      ∂finiteOriginalPinBlock 0 (Fintype.card E) U) ≤
    ∑ e, (2 * (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
      finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0))) *
        (finiteOriginalPinBlock 0 t U).real {W | finiteActiveOriginalQueryAt w f W t T ∅ = some e} := by
  let N := Fintype.card E
  let ν := Measure.pi (fun _ : Fin N => finiteUnitUniform)
  let μ := finiteOriginalPinBlock 0 t U
  let Y := fun s (W : ℕ → ℝ) (v : Fin N → ℝ) =>
    finiteJointHybridEval w f s W (finiteSeedExtension N V v) T ∅ ∅ false
  let C := fun W => ∫ v, |f (Y (t + 1) W v) - f (Y t W v)| ∂ν
  let H := fun W => ∫ Z, C Z ∂finiteOriginalPinBlock t (N - t) W
  let q := fun W => finiteActiveOriginalQueryAt w f W t T ∅
  let a := fun e => 2 * (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
    finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0))
  have hgap : ∀ A : Finset E × Finset E, |f A.1 - f A.2| ∈ Set.Icc (0 : ℝ) 1 := by
    intro A
    refine ⟨abs_nonneg _, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [(hf01 A.1).1, (hf01 A.1).2, (hf01 A.2).1, (hf01 A.2).2]
  have hCm : Measurable C :=
    finiteHybridPair_product_integral_measurable w f (fun A => |f A.1 - f A.2|) (t + 1) t V T
  have hC01 (W : ℕ → ℝ) : C W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteHybridPair_product_integral_mem_Icc w f (fun A => |f A.1 - f A.2|) hgap (t + 1) t W V T
  have hHm : Measurable H := probabilityKernel_unit_integral_measurable _
    (finiteOriginalPinBlock_measurable t (N - t)) C hCm hC01
  have hH01 (W : ℕ → ℝ) : H W ∈ Set.Icc (0 : ℝ) 1 := by
    have hi := integrable_of_unit_bounds (finiteOriginalPinBlock t (N - t) W) hCm hC01
    refine ⟨integral_nonneg (fun Z => (hC01 Z).1), ?_⟩
    simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun Z => (hC01 Z).2)
  have hHi := integrable_of_unit_bounds μ hHm hH01
  have hq : Measurable q := finiteActiveOriginalQueryAt_measurable w f t T ∅
  have hR := option_query_weight_integral μ q hq a
  have hle := integral_mono hHi hR.1 (fun W =>
    finiteActiveHybrid_switch_cost_le w hw f hf hf01 W V t T)
  have hsplit := finiteOriginalPinBlock_integral_split 0 t (N - t) U C hCm hC01
  simp only [Nat.zero_add] at hsplit
  rw [show t + (N - t) = N by dsimp [N]; omega] at hsplit
  change (∫ W, H W ∂μ) = ∫ W, C W ∂finiteOriginalPinBlock 0 N U at hsplit
  rw [hR.2, hsplit] at hle
  exact hle

end
end PottsContinuity.BD12
