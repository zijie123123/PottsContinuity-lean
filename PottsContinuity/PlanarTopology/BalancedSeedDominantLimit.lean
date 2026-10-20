module

public import PottsContinuity.PlanarTopology.BalancedSeedDominantBound
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- A large fixed seed has a dominant Left or Bottom connection probability
arbitrarily close to one, uniformly over all dimensions and balanced cells. -/
theorem balanced_seed_dominant_probability_eventually_gt
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ W H : ℕ,
      ∀ v x y : Fin (W+1) × Fin (H+1), RectangleSeedBalancedCell μ W H (2*r+2) v x y →
        1-ε < max (rectangleSeedLeftProbability μ W H (2*r+2) v)
          (rectangleSeedBottomProbability μ W H (2*r+2) v) := by
  have hθ : Tendsto (fun r : ℕ => μ.real (infiniteHit (latticeBox (0,0) r : Set LatticeVertex))) atTop (𝓝 1) := by
    have hh := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
      (infiniteHit_box_probability_tendsto_one μ hinfinite)
    simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_one] using hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_order.mp hθ).1 (1-ε^4) (by have hp := pow_pos hε 4; linarith))
  refine ⟨R,?_⟩
  intro r hr W H v x y hc
  by_contra hnot
  have hb := balanced_seed_dominant_complement_pow_four μ htranslation hFKG W H r v x y hc
  have hsmall : max (rectangleSeedLeftProbability μ W H (2*r+2) v)
      (rectangleSeedBottomProbability μ W H (2*r+2) v) ≤ 1-ε := le_of_not_gt hnot
  have hp := pow_le_pow_left₀ (le_of_lt hε) (show ε ≤ 1-max
    (rectangleSeedLeftProbability μ W H (2*r+2) v)
    (rectangleSeedBottomProbability μ W H (2*r+2) v) by linarith) 4
  linarith [hR r hr]

end
end PottsContinuity.PlanarTopology
