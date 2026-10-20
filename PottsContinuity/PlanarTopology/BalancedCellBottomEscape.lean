module

public import PottsContinuity.PlanarTopology.BalancedCellTranspose
public import PottsContinuity.PlanarTopology.BalancedCellLeftEscape
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Every sufficiently large fixed seed has balanced anchors escaping Bottom,
uniformly over both rectangle dimensions, without coordinate symmetry of the law. -/
theorem balanced_cells_eventually_far_bottom
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, 2*N+2 < W → N < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < v.2.val := by
  obtain ⟨R,hR⟩ := balanced_cells_eventually_far_left
    (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso))
    (transposeLaw_translation_invariant μ htranslation) (transposeLaw_FKG μ hFKG)
    (transposeLaw_dual_unique μ hunique) (transposeLaw_dual_infinite μ hdualInfinite)
    (configurationIsoLaw_infinite latticeTransposeIso μ hinfinite)
  refine ⟨R,?_⟩
  intro r hr M
  obtain ⟨N,hN⟩ := hR r hr M
  refine ⟨N,?_⟩
  intro W H hW hH v x y hc
  exact hN H W hH hW v.swap y.swap x.swap hc.transpose

/-- The two lower coordinate distances diverge simultaneously with a single
rectangle size threshold, for every admissible balanced cell. -/
theorem balanced_cells_eventually_far_left_bottom
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, N < W → N < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < v.1.val ∧ M < v.2.val := by
  obtain ⟨RL,hL⟩ := balanced_cells_eventually_far_left μ htranslation hFKG hunique hdualInfinite hinfinite
  obtain ⟨RB,hB⟩ := balanced_cells_eventually_far_bottom μ htranslation hFKG hunique hdualInfinite hinfinite
  refine ⟨max RL RB,?_⟩
  intro r hr M
  obtain ⟨NL,hNL⟩ := hL r (le_trans (le_max_left _ _) hr) M
  obtain ⟨NB,hNB⟩ := hB r (le_trans (le_max_right _ _) hr) M
  refine ⟨2*(NL+NB)+2,?_⟩
  intro W H hW hH v x y hc
  exact ⟨hNL W H (by omega) (by omega) v x y hc,
    hNB W H (by omega) (by omega) v x y hc⟩

end
end PottsContinuity.PlanarTopology
