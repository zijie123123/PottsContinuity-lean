module

public import PottsContinuity.PlanarTopology.BalancedCellBottomEscape
public import PottsContinuity.PlanarTopology.BalancedCellRightEscape

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Top escape follows from Right escape for the transposed law and transposed
reverse witnesses, without assuming coordinate symmetry. -/
theorem balanced_cells_eventually_far_top
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, 2*N+2 < W → N < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y → M < H-v.2.val := by
  obtain ⟨R,hR⟩ := balanced_cells_eventually_far_right
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

/-- All four distances of every balanced anchor from the anchor-domain boundary
diverge uniformly as both rectangle dimensions increase. -/
theorem balanced_cells_eventually_far_all_sides
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ M : ℕ, ∃ N : ℕ, ∀ W H : ℕ, N < W → N < H →
      ∀ v x y : Fin (W+1) × Fin (H+1),
        RectangleSeedBalancedCell μ W H (2*r+2) v x y →
          M < v.1.val ∧ M < v.2.val ∧ M < W-v.1.val ∧ M < H-v.2.val := by
  obtain ⟨RA,hA⟩ := balanced_cells_eventually_far_left_bottom μ htranslation hFKG hunique hdualInfinite hinfinite
  obtain ⟨RR,hR⟩ := balanced_cells_eventually_far_right μ htranslation hFKG hunique hdualInfinite hinfinite
  obtain ⟨RT,hT⟩ := balanced_cells_eventually_far_top μ htranslation hFKG hunique hdualInfinite hinfinite
  refine ⟨max RA (max RR RT),?_⟩
  intro r hr M
  have hrA : RA ≤ r := le_trans (le_max_left _ _) hr
  have hrR : RR ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hrT : RT ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  obtain ⟨NA,hNA⟩ := hA r hrA M
  obtain ⟨NR,hNR⟩ := hR r hrR M
  obtain ⟨NT,hNT⟩ := hT r hrT M
  refine ⟨2*(NA+NR+NT)+2,?_⟩
  intro W H hW hH v x y hc
  obtain ⟨hleft,hbottom⟩ := hNA W H (by omega) (by omega) v x y hc
  exact ⟨hleft,hbottom,hNR W H (by omega) (by omega) v x y hc,
    hNT W H (by omega) (by omega) v x y hc⟩

end
end PottsContinuity.PlanarTopology
