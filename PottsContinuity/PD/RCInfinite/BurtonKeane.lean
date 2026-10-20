-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/BurtonKeane.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.TrifurcationProbability
public import PottsContinuity.PD.RCInfinite.TrifurcationSurgery
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A positive three-cluster event can be changed on finitely many box-incident
edges to produce a trifurcation with positive probability. -/
theorem exists_positive_trifurcation_of_positive_three_clusters
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (hpos : 0 < μ.real (atLeastInfiniteClusters 3)) :
    ∃ v : LatticeVertex, 0 < μ.real (trifurcationEvent v) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨xs, hxspos⟩ := exists_positive_infiniteClusterWitnesses μ hpos
  let S : Finset LatticeVertex := Finset.univ.image xs
  obtain ⟨n, hn⟩ := exists_box_containing_finset S
  have hxsBox : ∀ j, xs j ∈ latticeBox (0, 0) n := by
    intro j
    apply hn (xs j)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  obtain ⟨exits, hcellpos⟩ := exists_positive_boxExitTriple μ n xs hxsBox hxspos
  have hcell_nonempty : (boxExitTripleCell n xs exits).Nonempty := by
    by_contra hne
    have heq : boxExitTripleCell n xs exits = ∅ := by
      ext ω
      constructor
      · intro hω
        exact (hne ⟨ω, hω⟩).elim
      · simp
    simp [heq] at hcellpos
  obtain ⟨ω₀, hω₀⟩ := hcell_nonempty
  let hdist := boxExitTripleCell_outside_injective ω₀ xs exits hω₀
  obtain ⟨U, hTU, H, hHG, _htree, v, hsep⟩ :=
    exists_box_exit_connector_separator n exits
  let f := boxExitSubembedding exits hdist U
  let ξ := boxTreeEdgeState H f
  have himage : 0 < μ.real
      (setEdges (boxIncidentEdges n) ξ '' boxExitTripleCell n xs exits) :=
    setEdges_image_real_pos θ i μ hμ (boxIncidentEdges n) ξ
      (measurableSet_boxExitTripleCell n xs exits) hcellpos
  have hsubset : setEdges (boxIncidentEdges n) ξ '' boxExitTripleCell n xs exits ⊆
      trifurcationEvent (f v) := by
    rintro η ⟨ω, hω, rfl⟩
    change isTrifurcationAt (setEdges (boxIncidentEdges n) ξ ω) (f v)
    simpa only [f, ξ, boxExitSubembedding] using
      (boxExitTripleCell_surgery_trifurcation ω xs exits hω U hTU H hHG v hsep)
  have hprob : 0 < μ.real (trifurcationEvent (f v)) :=
    lt_of_lt_of_le himage (measureReal_mono hsubset)
  exact ⟨f v, hprob⟩

/-- Three or more infinite clusters have probability zero for either frozen
random-cluster limit. -/
theorem isRCInfiniteVolumeLimit_atLeastThree_probability_zero
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    μ.real (atLeastInfiniteClusters 3) = 0 := by
  by_contra hzero
  have hpos : 0 < μ.real (atLeastInfiniteClusters 3) :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero)
  obtain ⟨v, hv⟩ := exists_positive_trifurcation_of_positive_three_clusters θ i μ hμ hpos
  have htranslate := trifurcation_probability_translation θ i μ hμ v (0, 0)
  have hv0 : μ.real (trifurcationEvent v) = μ.real (trifurcationEvent (0, 0)) := by
    simpa [latticeTranslate] using htranslate
  rw [hv0, isRCInfiniteVolumeLimit_origin_trifurcation_probability_zero θ i μ hμ] at hv
  exact (lt_irrefl 0) hv

/-- Every infinite-volume free or wired limit has at most one infinite open
cluster almost surely. -/
theorem isRCInfiniteVolumeLimit_atMostOneInfiniteCluster
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω := by
  let : IsProbabilityMeasure μ := hμ.1
  rcases infinite_cluster_count_zero_one_or_unbounded θ i μ hμ with hzero | hone | hunbounded
  · have hc : μ (exactInfiniteClusters 0)ᶜ = 0 := by
      rw [measure_compl (measurableSet_exactInfiniteClusters 0) (measure_ne_top μ _),
        measure_univ, hzero, tsub_self]
    have hae : ∀ᵐ ω ∂μ, ω ∈ exactInfiniteClusters 0 := ae_iff.mpr hc
    filter_upwards [hae] with ω hω
    have hnotone : ω ∉ atLeastInfiniteClusters 1 := hω.2
    have hnotwo : ω ∉ atLeastInfiniteClusters 2 := by
      intro htwo
      exact hnotone (atLeastInfiniteClusters_antitone (by omega) htwo)
    by_contra hnotuni
    exact hnotwo ((atLeastTwo_iff_not_atMostOne ω).mpr hnotuni)
  · have hc : μ (exactInfiniteClusters 1)ᶜ = 0 := by
      rw [measure_compl (measurableSet_exactInfiniteClusters 1) (measure_ne_top μ _),
        measure_univ, hone, tsub_self]
    have hae : ∀ᵐ ω ∂μ, ω ∈ exactInfiniteClusters 1 := ae_iff.mpr hc
    filter_upwards [hae] with ω hω
    by_contra hnotuni
    exact hω.2 ((atLeastTwo_iff_not_atMostOne ω).mpr hnotuni)
  · have hae3 : ∀ᵐ ω ∂μ, ω ∈ atLeastInfiniteClusters 3 := by
      filter_upwards [hunbounded] with ω hω
      exact hω 3
    have hc : μ (atLeastInfiniteClusters 3)ᶜ = 0 := ae_iff.mp hae3
    have hfull : μ (atLeastInfiniteClusters 3) = 1 := by
      simpa only [hc, add_zero, measure_univ] using
        measure_add_measure_compl (μ := μ) (measurableSet_atLeastInfiniteClusters 3)
    have hreal : μ.real (atLeastInfiniteClusters 3) = 1 := by
      simp [Measure.real, hfull]
    rw [isRCInfiniteVolumeLimit_atLeastThree_probability_zero θ i μ hμ] at hreal
    norm_num at hreal

end
end PottsContinuity.PD.RCInfinite
