module

public import PottsContinuity.PlanarTopology.DRTFixedEnlargementMaximum
public import PottsContinuity.PlanarTopology.OrdinaryRectangleDualityLaw

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
noncomputable section

/-- The exact dual rectangles are the two fixed enlargements of the inner
rectangle (n-1,k-1). Thus their large maximum forces the original small minimum. -/
theorem drt_crossing_min_eventually_lt
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n k : ℕ, N < n → N < k →
      min (μ.real (verticalRectangle (0,0) n k))
        (μ.real (horizontalRectangle (0,0) n k)) < ε := by
  let ν := μ.map wholePlaneDualConfigurationHomeomorph
  have hνν : ν.map wholePlaneDualConfigurationHomeomorph = μ := wholePlaneDualLaw_twice μ htranslation
  have hu : ∀ᵐ η ∂ν, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph η) := by
    apply (wholePlaneDualLaw_ae_iff ν _).mp
    rwa [hνν]
  have hi : ∀ᵐ η ∂ν, wholePlaneDualConfigurationHomeomorph η ∈ infiniteClusterEvent := by
    apply (wholePlaneDualLaw_ae_iff ν _).mp
    rwa [hνν]
  obtain ⟨N,hN⟩ := drt_fixed_enlargement_crossing_max_eventually_gt ν
    (wholePlaneDualLaw_translation_invariant μ htranslation) (wholePlaneDualLaw_FKG μ hFKG)
    hu hi ((wholePlaneDualLaw_ae_iff μ _).mpr hdualUnique)
    ((wholePlaneDualLaw_ae_iff μ _).mpr hdualInfinite) 2 2 ε hε
  refine ⟨N+2,?_⟩
  intro n k hn hk
  have hm := hN (n-1) (k-1) (by omega) (by omega)
  have hn₁ : n-1+1 = n := by omega
  have hk₁ : k-1+1 = k := by omega
  have hn₂ : n-1+2 = n+1 := by omega
  have hk₂ : k-1+2 = k+1 := by omega
  rw [hn₂,hk₂] at hm
  have hh : ν.real (horizontalRectangle (0,0) (n+1) (k-1)) =
      1-μ.real (verticalRectangle (0,0) n k) := by
    simpa only [hk₁] using dualLaw_horizontalRectangle_eq_one_sub_vertical μ htranslation n (k-1)
  have hv : ν.real (verticalRectangle (0,0) (n-1) (k+1)) =
      1-μ.real (horizontalRectangle (0,0) n k) := by
    simpa only [hn₁] using dualLaw_verticalRectangle_eq_one_sub_horizontal μ htranslation (n-1) k
  rw [hh,hv] at hm
  have heq : max (1-μ.real (verticalRectangle (0,0) n k))
      (1-μ.real (horizontalRectangle (0,0) n k)) =
      1-min (μ.real (verticalRectangle (0,0) n k)) (μ.real (horizontalRectangle (0,0) n k)) := by
    by_cases hvh : μ.real (verticalRectangle (0,0) n k) ≤ μ.real (horizontalRectangle (0,0) n k)
    · rw [min_eq_left hvh,max_eq_left (by linarith)]
    · rw [min_eq_right (le_of_not_ge hvh),max_eq_right (by linarith)]
  rw [heq] at hm
  linarith

/-- The small-minimum part of DRT's rectangle lemma, along every pair of
diverging integral side lengths and with the original actual crossing events. -/
theorem drt_crossing_min_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hdualUnique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hdualInfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent)
    (n k : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => min (μ.real (verticalRectangle (0,0) (n j) (k j)))
      (μ.real (horizontalRectangle (0,0) (n j) (k j)))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun _ => lt_of_lt_of_le hb
      (le_min measureReal_nonneg measureReal_nonneg))
  · intro b hb
    obtain ⟨N,hN⟩ := drt_crossing_min_eventually_lt μ htranslation hFKG
      hdualUnique hdualInfinite hunique hinfinite b hb
    filter_upwards [hn.eventually_gt_atTop N,hk.eventually_gt_atTop N] with j hjn hjk
    exact hN (n j) (k j) hjn hjk

end
end PottsContinuity.PlanarTopology
