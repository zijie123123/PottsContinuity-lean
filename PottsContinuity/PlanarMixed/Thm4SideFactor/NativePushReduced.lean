module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushReducedDefinitions
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePush

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.Duality BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance nativePushReducedProp (p : Prop) : Decidable p := Classical.propDecidable p
local instance nativePushReducedEdgeEq (m : ℕ) : DecidableEq (nativeSideFullGraph m).edgeSet := Classical.decEq _
local instance nativePushReducedRemaining (m : ℕ) :
    Fintype (RemainingConfiguration (nativeSideFullGraph m) (nativeSideWiredEdges m)) := Fintype.ofFinite _

theorem nativeSideWiredEdges_prewired (m : ℕ) (u v : NativeSideVertex m)
    (huv : (nativeSideFullGraph m).Adj u v)
    (he : (⟨s(u,v),(nativeSideFullGraph m).mem_edgeSet.mpr huv⟩ : (nativeSideFullGraph m).edgeSet) ∈
      nativeSideWiredEdges m) : (nativeSideFullBoundary m).partition.r u v := by
  exact Or.inr ((mem_nativeSideWiredEdges_pair m u v huv).mp he)

theorem nativeSideWiredEdges_band_internal (m : ℕ) (hm : 1 ≤ m)
    (u v : RectangleVertex (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1))
    (huv : (rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1)).Adj u v)
    (he : embeddedEdgeEmbedding _ (nativeSideFullGraph m)
      (Push.rectangleBandEmbedding (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega))
      (Push.rectangleBandEmbedding_map_le (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega))
      ⟨s(u,v),(rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1)).mem_edgeSet.mpr huv⟩ ∈
      nativeSideWiredEdges m) :
    (u.val.1 = -16*(m:ℤ)-1 ∧ v.val.1 = -16*(m:ℤ)-1) ∨
    (u.val.1 = 16*(m:ℤ) ∧ v.val.1 = 16*(m:ℤ)) := by
  let f := Push.rectangleBandEmbedding (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)
  have hmap : (nativeSideFullGraph m).Adj (f u) (f v) := huv
  have hhe : (⟨s(f u,f v),(nativeSideFullGraph m).mem_edgeSet.mpr hmap⟩ :
    (nativeSideFullGraph m).edgeSet) ∈ nativeSideWiredEdges m := he
  have hh := (mem_nativeSideWiredEdges_pair m (f u) (f v) hmap).mp hhe
  change (u.val.1 = -16*(m:ℤ)-1 ∨ u.val.1 = 16*(m:ℤ) ∨ u.val.2 = 15*(m:ℤ)) ∧
    (v.val.1 = -16*(m:ℤ)-1 ∨ v.val.1 = 16*(m:ℤ) ∨ v.val.2 = 15*(m:ℤ)) at hh
  have hu := (mem_latticeRectangle (-16*(m:ℤ)-1,0) u.val (32*m+1) (4*m-1)).mp u.property
  have hv := (mem_latticeRectangle (-16*(m:ℤ)-1,0) v.val (32*m+1) (4*m-1)).mp v.property
  have hd : |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1 := huv
  simp only [abs_eq_max_neg] at hd
  dsimp only [Prod.fst,Prod.snd] at hu hv
  omega

theorem nativeSideCrossing_sdiff_wiredEdges (m : ℕ) (hm : 1 ≤ m)
    (C : Configuration (nativeSideFullGraph m)) :
    C \ nativeSideWiredEdges m ∈
      Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega) ↔
    C ∈ Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega) := by
  apply Push.embedded_arcsConnection_sdiff_internal_edges
  intro u v huv he
  have h := nativeSideWiredEdges_band_internal m hm u v huv he
  have hr : -16*(m:ℤ)-1 + ((32*m+1:ℕ):ℤ) = 16*(m:ℤ) := by omega
  simpa only [hr,Set.mem_ofPred_eq] using h

theorem nativeSideReducedCrossingEvent_isUpperSet (m : ℕ) :
    IsUpperSet (nativeSideReducedCrossingEvent m) := by
  intro A B hAB hA
  have hfull := (edgeRestrictionConfigurationEquiv_le_iff
    (nativeSideFullGraph m) (nativeSideWiredEdges m) A B).mpr hAB
  have hband := embeddedConfigurationRestriction_monotone
    (rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1)) (nativeSideFullGraph m)
    (Push.rectangleBandEmbedding (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega))
    (Push.rectangleBandEmbedding_map_le (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)) hfull
  exact (arcsConnectionEvent_isUpperSet _ _) hband hA

theorem nativeSideReduced_crossing_measure_eq (q : Set.Ici (1:ℝ)) (m : ℕ) (hm : 1 ≤ m) :
    measure (nativeSideReducedGraph m) (selfDualParameters q) (nativeSideFullBoundary m)
      (nativeSideReducedCrossingEvent m) =
    measure (nativeSideFullGraph m) (selfDualParameters q) (nativeSideFullBoundary m)
      (Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)) := by
  let E := Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1) (4*m-1) (15*m) (by omega)
  let H := nativeSideFullGraph m
  let R := nativeSideWiredEdges m
  let θ := selfDualParameters q
  let ξ := nativeSideFullBoundary m
  have hred := congrArg (fun μ : PMF (RemainingConfiguration H R) =>
    μ.toMeasure {ω | ω.val ∈ E}) (law_edgeRestriction_map H θ ξ R)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hred
  change measure (nativeSideReducedGraph m) θ ξ (nativeSideReducedCrossingEvent m) = _ at hred
  rw [hred]
  have hsplit := law_map_remove H θ ξ R (nativeSideWiredEdges_prewired m)
  have hp := congrArg (fun μ : PMF (RemainingConfiguration H R) =>
    μ.toMeasure {ω | ω.val ∈ E}) hsplit
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hp
  rw [← hp]
  congr 1
  ext C
  exact nativeSideCrossing_sdiff_wiredEdges m hm C

theorem nativeSideReduced_crossing_uniform_pos (q : Set.Ici (1:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c ≤ (measure (nativeSideReducedGraph m) (selfDualParameters q) (nativeSideFullBoundary m)
        (nativeSideReducedCrossingEvent m)).toReal := by
  obtain ⟨c,hc,hbound⟩ := nativeSide_crossing_uniform_pos q
  refine ⟨c,hc,fun m hm => ?_⟩
  rw [nativeSideReduced_crossing_measure_eq q m hm]
  have hb := hbound m hm
  rw [nativeSideCrossingProbability_eq_rectangleBand q m hm] at hb
  exact hb

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
