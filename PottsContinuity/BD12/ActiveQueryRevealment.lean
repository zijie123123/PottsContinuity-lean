module

public import PottsContinuity.BD12.QueryNoRepetition
public import PottsContinuity.BD12.ActiveQueryRegularity
public import PottsContinuity.BD12.OriginalPinBlockSplit
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic
public import Mathlib.Order.CompletePartialOrder

/-! Identify the time sum of active-query probabilities with the actual event
that the exploration queries an edge. Freshness gives disjoint time fibres. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- A measurable event determined by a strict original prefix has the same
probability under the prefix law and under its completion by future uniforms. -/
theorem finiteOriginalPinBlock_prefix_event_probability (N t : ℕ) (ht : t ≤ N)
    (U : ℕ → ℝ) (S : Set (ℕ → ℝ)) (hS : MeasurableSet S)
    (hprefix : ∀ W Z, (∀ i, i < t → W i = Z i) → (W ∈ S ↔ Z ∈ S)) :
    (finiteOriginalPinBlock 0 N U).real S = (finiteOriginalPinBlock 0 t U).real S := by
  let g := S.indicator (fun _ : ℕ → ℝ => (1 : ℝ))
  have hg : Measurable g := measurable_const.indicator hS
  have hg01 (W : ℕ → ℝ) : g W ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hW : W ∈ S <;> simp [g, hW]
  have hfuture (W : ℕ → ℝ) :
      (∫ Z, g Z ∂finiteOriginalPinBlock t (N - t) W) = g W := by
    calc
      _ = ∫ _Z : ℕ → ℝ, g W ∂finiteOriginalPinBlock t (N - t) W := by
        apply integral_congr_ae
        filter_upwards [finiteOriginalPinBlock_ae_past t (N - t) W] with Z hZ
        have hmem := hprefix Z W hZ
        by_cases hW : W ∈ S
        · simp [g, hW, hmem.mpr hW]
        · have hZn : Z ∉ S := fun hz => hW (hmem.mp hz)
          simp [g, hW, hZn]
      _ = g W := by simp
  have h := finiteOriginalPinBlock_integral_split 0 t (N - t) U g hg hg01
  simp only [Nat.zero_add] at h
  rw [show t + (N - t) = N by omega] at h
  simp_rw [hfuture] at h
  change (∫ W, S.indicator (fun _ => (1 : ℝ)) W ∂finiteOriginalPinBlock 0 t U) =
    ∫ W, S.indicator (fun _ => (1 : ℝ)) W ∂finiteOriginalPinBlock 0 N U at h
  simp only [integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one] at h
  exact h.symm

variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Option E)] [MeasurableSingletonClass (Option E)]

/-- The time sum in the query-sum OSSS inequality is exactly the usual edge
revealment probability under the complete original uniform input law. -/
theorem finiteActiveOriginalQueryAt_sum_eq_revealment
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U : ℕ → ℝ) (T : FiniteRevealTree E ∅) (e : E) :
    (∑ t ∈ Finset.range (Fintype.card E), (finiteOriginalPinBlock 0 t U).real
      {W | finiteActiveOriginalQueryAt w f W t T ∅ = some e}) =
    (finiteOriginalPinBlock 0 (Fintype.card E) U).real
      {W | ∃ t ∈ Finset.range (Fintype.card E), finiteActiveOriginalQueryAt w f W t T ∅ = some e} := by
  let N := Fintype.card E
  let μ := finiteOriginalPinBlock 0 N U
  let S := fun t => {W | finiteActiveOriginalQueryAt w f W t T ∅ = some e}
  have hS (t : ℕ) : MeasurableSet (S t) := finiteActiveOriginalQueryAt_fibre_measurableSet w f t T ∅ e
  have hp (t : ℕ) (ht : t ∈ Finset.range N) :
      (finiteOriginalPinBlock 0 t U).real (S t) = μ.real (S t) := by
    apply Eq.symm
    apply finiteOriginalPinBlock_prefix_event_probability N t (Nat.le_of_lt (Finset.mem_range.mp ht)) U (S t) (hS t)
    intro W Z hWZ
    exact congrArg (fun q : Option E => q = some e)
      (finiteActiveOriginalQueryAt_congr_prefix w f W Z t hWZ T ∅) |>.to_iff
  have hdis : Set.PairwiseDisjoint (↑(Finset.range N)) S := by
    intro t _ s _ hts
    apply Set.disjoint_left.mpr
    intro W hWt hWs
    exact hts (finiteActiveOriginalQueryAt_time_unique w f W t s T ∅ e hWt hWs)
  have hu := measureReal_biUnion_finset (μ := μ) hdis (fun t _ => hS t)
  calc
    _ = ∑ t ∈ Finset.range N, μ.real (S t) := Finset.sum_congr rfl hp
    _ = μ.real (⋃ t ∈ Finset.range N, S t) := hu.symm
    _ = _ := by congr 1; ext W; simp [S, N]

end
end PottsContinuity.BD12
