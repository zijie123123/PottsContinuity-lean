module

public import PottsContinuity.BD12.ActiveQueryCostAverage
public import PottsContinuity.BD12.HybridPairSeedIntegral
public import PottsContinuity.BD12.HybridVarianceTelescoping
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite monotone-measure OSSS with literal active-query probabilities summed
by time. The hybrid representation, stopping, Harris estimates and original
prefix averages are all proved, rather than supplied as interface assumptions. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]
    [MeasurableSpace (Option E)] [MeasurableSingletonClass (Option E)]

/-- OSSS with each edge weighted by the sum of its actual active-query
probabilities over exploration times. No revealment or covariance bound is
assumed. Identifying that sum with the probability of querying the edge at
some time is a separate no-repeated-query step. -/
theorem finite_osss_query_sum
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    finitePinnedMean w ∅ ∅ (fun A => f A ^ 2) - (finitePinnedMean w ∅ ∅ f) ^ 2 ≤
      ∑ e, (∑ t ∈ Finset.range (Fintype.card E),
        (finiteOriginalPinBlock 0 t U).real {W | finiteActiveOriginalQueryAt w f W t T ∅ = some e}) *
        (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
          finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0)) := by
  let N := Fintype.card E
  let background := fun i => (U i, V i)
  let μ := finiteHybridSeedWindow 0 U background 0 N
  let Y := fun s (S : ℕ → ℝ × ℝ) =>
    finiteJointHybridEval w f s (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false
  let c := fun e => finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
    finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0)
  let p := fun t e => (finiteOriginalPinBlock 0 t U).real
    {W | finiteActiveOriginalQueryAt w f W t T ∅ = some e}
  have hgap : ∀ A : Finset E × Finset E, |f A.1 - f A.2| ∈ Set.Icc (0 : ℝ) 1 :=
    fun A => unit_interval_abs_sub _ _ (hf01 A.1) (hf01 A.2)
  have htime (t : ℕ) (ht : t ∈ Finset.range N) :
      (∫ S, |f (Y (t + 1) S) - f (Y t S)| ∂μ) ≤ ∑ e, (2 * c e) * p t e := by
    have h := finiteActiveHybrid_switch_cost_average_le w hw f hf hf01 U V t
      (Nat.le_of_lt (Finset.mem_range.mp ht)) T
    have heq := finiteHybridPair_product_block_integral_eq_seedWindow w f
      (fun A => |f A.1 - f A.2|) hgap (t + 1) t U V background T
    rw [heq] at h
    exact h
  have hsum := Finset.sum_le_sum (fun t ht => htime t ht)
  have hvar := finite_hybrid_variance_telescoping w f hf01 U background T
  change _ ≤ (1 / 2 : ℝ) * ∑ t ∈ Finset.range N, ∫ S, |f (Y (t + 1) S) - f (Y t S)| ∂μ at hvar
  have h := hvar.trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have heq : (1 / 2 : ℝ) * (∑ t ∈ Finset.range N, ∑ e, (2 * c e) * p t e) =
      ∑ e, (∑ t ∈ Finset.range N, p t e) * c e := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    ring
  rw [heq] at h
  exact h

end
end PottsContinuity.BD12
