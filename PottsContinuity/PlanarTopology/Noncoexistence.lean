module

public import PottsContinuity.PlanarTopology.DRTActualHeightSelector
public import PottsContinuity.PlanarTopology.DRTCrossingMinimum

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
noncomputable section

/-- A translation-invariant positively associated planar bond law cannot have
unique existing infinite clusters both in the original and complementary-dual
configurations. This is Theorem 1.5 of Duminil-Copin–Raoufi–Tassion (arXiv:1705.03104v2) on the
square lattice, proved along its proof (Lemma 4.1 there). -/
theorem planar_noncoexistence
    (μ : Measure LatticeConfiguration) (hprob : IsProbabilityMeasure μ)
    (htranslation : ∀ a : LatticeVertex, μ.map (latticeConfigurationTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hprimal : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent)
    (hdual : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω) ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) : False := by
  let : IsProbabilityMeasure μ := hprob
  have hpu : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω := hprimal.mono (fun _ h => h.1)
  have hpi : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent := hprimal.mono (fun _ h => h.2)
  have hdu : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω) :=
    hdual.mono (fun _ h => h.1)
  have hdi : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent :=
    hdual.mono (fun _ h => h.2)
  obtain ⟨k,hbalance,hk⟩ := exists_actual_balanced_height_tendsto_atTop μ htranslation hFKG hdu hdi hpu hpi
  have hn : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_id
  have hk' : Tendsto (fun n => k n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (k n)) hk
  have hlarge := drt_fixed_enlargement_crossing_max_tendsto_one μ htranslation hFKG
    hdu hdi hpu hpi 0 1 (fun n => n+1) k hn hk
  simp only [Nat.add_zero] at hlarge
  have hsmall := drt_crossing_min_tendsto_zero μ htranslation hFKG hdu hdi hpu hpi
    (fun n => n+1) k hn hk
  have hsmall' := drt_crossing_min_tendsto_zero μ htranslation hFKG hdu hdi hpu hpi
    (fun n => n+1) (fun n => k n+1) hn hk'
  exact drt_crossing_contradiction_of_crossingLimits
    (fun n K => μ.real (horizontalRectangle (0,0) (n+1) K))
    (fun n K => μ.real (verticalRectangle (0,0) (n+1) K)) k
    (fun n => (hbalance n).1) (fun n => le_of_lt (hbalance n).2) hlarge hsmall hsmall'

end
end PottsContinuity.PlanarTopology
