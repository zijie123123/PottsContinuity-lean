module

public import PottsContinuity.BD12.ReverseThresholdContracts
public import PottsContinuity.BD12.DualParameterOrder
public import PottsContinuity.Coincidence.Exports
public import PottsContinuity.Infinite.MeasurableFKG
public import PottsContinuity.Infinite.Translation
public import PottsContinuity.Foundations.EveryExhaustion

/-! Reverse genuine-threshold assembly with separate coincidence and planar inputs. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.FK.Medial PD.Duality PD.RCInfinite
noncomputable section

/-- Dense free/wired coincidence and the general planar non-coexistence
statement imply the genuine reverse bound. Every cluster-existence,
uniqueness, symmetry, association and dual-law premise is discharged. -/
theorem selfDual_le_genuine_criticalPoint_of_nonCoexistence_and_coincidence
    (q : Set.Ici (1 : ℝ)) (pc : ℝ) (hpc : IsRCCriticalPoint q pc)
    (hplanar : PlanarNonCoexistenceContract) (hcoincidence : DenseCoincidenceContract q) :
    (PD.rcCriticalParameter q : ℝ) ≤ pc := by
  by_contra hn
  have hpcs : pc < (PD.rcCriticalParameter q : ℝ) := lt_of_not_ge hn
  obtain ⟨t,ht,μ₀,μ₁,hμ₀,hμ₁,heq⟩ := hcoincidence pc (PD.rcCriticalParameter q)
    hpc.1.1 hpcs (rcCriticalParameter_mem_Ioo q).2
  let q' : Set.Ioi (0 : ℝ) := ⟨(q : ℝ), (show (0 : ℝ) < (q : ℝ) from lt_of_lt_of_le one_pos q.property)⟩
  have ht0 : 0 < (t : ℝ) := hpc.1.1.trans ht.1
  have ht1 : (t : ℝ) < 1 := ht.2.trans (rcCriticalParameter_mem_Ioo q).2
  let θ := Infinite.pdParameters t q' ht0 ht1 q.property
  have hμ₀θ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀ := by
    change IsRCInfiniteVolumeLimit t q' 0 μ₀
    exact hμ₀
  have hae₀ : ∀ᵐ ω ∂μ₀, atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent :=
    Coincidence.coincident_free_limit_unique_infinite_cluster q pc hpc t ht.1 ht0 ht1
      μ₀ μ₁ hμ₀ hμ₁ heq
  obtain ⟨νraw,hνraw⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (dualParameters θ).toP (dualParameters θ).toQ (dualParameters θ).property 1
  let ν : Measure LatticeConfiguration := νraw
  have hν : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 ν := hνraw
  have hpstar : pc < ((dualParameters θ).toP : ℝ) := by
    exact hpcs.trans (selfDual_lt_dualParameter_of_lt q t ⟨ht0,ht1⟩ ht.2)
  obtain ⟨νc,hνc,_,hpositive⟩ := hpc.2 (dualParameters θ).toP
  have heqc : νc = ν := WellDefined.limit_unique _ _ 1 νc ν hνc hν
  have hpos : 0 < ν (infiniteAt (0,0)) := by
    rw [← heqc]
    exact hpositive hpstar
  have hνPD := Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hν
  let : IsProbabilityMeasure ν := hν.1
  have hfull : ν infiniteClusterEvent = 1 :=
    (infiniteCluster_eq_one_iff_origin_pos _ _ (dualParameters θ).property 1 ν hνPD).mpr hpos
  have hexists : ∀ᵐ ω ∂ν, ω ∈ infiniteClusterEvent := by
    apply ae_iff.mpr
    change ν infiniteClusterEventᶜ = 0
    rw [measure_compl measurableSet_infiniteClusterEvent (measure_ne_top ν _),
      measure_univ, hfull, tsub_self]
  have haeν : ∀ᵐ ω ∂ν, atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent :=
    (isRCInfiniteVolumeLimit_atMostOneInfiniteCluster (dualParameters θ) 1 ν hνPD).and hexists
  have hmap : μ₀.map wholePlaneDualConfigurationHomeomorph = ν :=
    free_limit_map_dual θ μ₀ ν hμ₀θ hν
  have haedual : ∀ᵐ ω ∂μ₀,
      atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω) ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent := by
    apply ae_of_ae_map (μ := μ₀)
      (p := fun ω => atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent)
      wholePlaneDualConfigurationHomeomorph_measurable.aemeasurable
    rw [hmap]
    exact haeν
  exact hplanar μ₀ hμ₀.1
    (Infinite.infinite_volume_translation_invariant t q' q.property 0 μ₀ hμ₀)
    (Infinite.free_infinite_FKG_measurable t q' ht0 ht1 q.property μ₀ hμ₀)
    hae₀ haedual

end
end PottsContinuity.BD12
