module

public import PottsContinuity.Thm4.FiniteParameterContinuity
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK Filter Topology
noncomputable section

/-- Closed inequalities between continuous functions extend to q=4 from below.
The approximation stays in [3,4), hence always in the admissible FK range. -/
theorem continuous_le_at_four (f g : Set.Ici (1 : ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : Set.Ici (1 : ℝ), q.val < 4 → f q ≤ g q) :
    f ⟨4, by norm_num⟩ ≤ g ⟨4, by norm_num⟩ := by
  let r : ℕ → Set.Ici (1 : ℝ) := fun n =>
    ⟨4 - 1 / ((n : ℝ) + 1), by
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
      change (1 : ℝ) ≤ 4 - 1 / ((n : ℝ) + 1)
      linarith⟩
  have hr : ∀ n, (r n).val < 4 := by
    intro n
    dsimp [r]
    have hp : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    linarith
  have hlim : Tendsto r atTop (𝓝 (⟨4, by norm_num⟩ : Set.Ici (1 : ℝ))) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n : ℕ => 4 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (4 : ℝ))
    simpa using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact le_of_tendsto_of_tendsto ((hf.tendsto _).comp hlim) ((hg.tendsto _).comp hlim)
    (Eventually.of_forall (fun n => h (r n) (hr n)))

/-- Uniform upper bounds pass to the endpoint by the same finite-volume limit. -/
theorem fkc_event_upper_bound_at_four {V : Type*} [Finite V] (G : SimpleGraph V)
    (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition V)
    (s : Set (Configuration G)) (c : ℝ)
    (h : ∀ q : PottsContinuity.FKC.ClusterWeight,
      (PottsContinuity.FKC.FiniteFK.measure G q ξ s).toReal ≤ c) :
    (measure G (selfDualParameters ⟨4, by norm_num⟩) (fkcBoundaryToPD ξ) s).toReal ≤ c := by
  apply continuous_le_at_four
    (fun q => (measure G (selfDualParameters q) (fkcBoundaryToPD ξ) s).toReal) (fun _ => c)
    (continuous_selfDual_eventProbability G (fkcBoundaryToPD ξ) s) continuous_const
  intro q hq
  have hbound := h ⟨q.val, q.property, hq⟩
  rw [fkc_measure_eq] at hbound
  exact hbound

end
end PottsContinuity.Thm4
