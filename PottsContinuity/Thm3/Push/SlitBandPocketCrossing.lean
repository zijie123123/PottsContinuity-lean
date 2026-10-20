module

public import PottsContinuity.Thm3.Push.SlitBandPocketLaw
public import PottsContinuity.Thm3.Push.TwoCutPocketCrossing
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance slitBandPocketCrossingEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Every actual band crossing retains an actual open segment in the
pocket-reduced band, connecting the original separately wired cut arcs. -/
theorem slit_band_pockets_connection_restricts {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
    (C : Configuration (rankedBandGraph (graph M x y) (D.rank hM hy)))
    (hC : C ∈ arcsConnectionEvent _ (rankedBandFirstArc (D.rank hM hy)) (rankedBandSecondArc (D.rank hM hy))) :
    let H := rankedBandGraph (graph M x y) (D.rank hM hy)
    let S := slitBandPocketCarrier D hM hy
    embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S) (pocketInduced_map_le H S) C ∈
      arcsConnectionEvent (H.induce S) {u | D.rank hM hy u.val.val = 1} {v | D.rank hM hy v.val.val = 3} := by
  classical
  let H := rankedBandGraph (graph M x y) (D.rank hM hy)
  let S := slitBandPocketCarrier D hM hy
  obtain ⟨u,hu,v,hv,p⟩ := hC
  obtain ⟨p⟩ := p
  let f : openGraph H C →g graph M x y := {
    toFun := Subtype.val
    map_rel' := fun h => openGraph_le H C h }
  have hs := slit_crosscuts_cross_seeded_exteriors D hM
  obtain ⟨a,ha,b,hb,q,hq⟩ := twoCutPockets_crossing_segment_map (graph M x y)
    (openGraph H C) f Subtype.val_injective
    {w | w ∈ D.first.support} {w | w ∈ D.second.support} (alpha M x ∪ beta M x y)
    hs.1 hs.2 p ((D.rank_first_iff hM hy u.val).mp hu) ((D.rank_second_iff hM hy v.val).mp hv)
  have hqS : ∀ z ∈ q.support, z ∈ S := hq
  let j : ((openGraph H C).induce S) →g openGraph (H.induce S)
      (embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S) (pocketInduced_map_le H S) C) := {
    toFun := id
    map_rel' := fun {u v} h => (embeddedRestriction_openGraph_adj_iff _ H _
      (pocketInduced_map_le H S) C u v).mpr ⟨openGraph_le H C h,h⟩ }
  exact ⟨⟨a,hqS a q.start_mem_support⟩,(D.rank_first_iff hM hy a.val).mpr ha,
    ⟨b,hqS b q.end_mem_support⟩,(D.rank_second_iff hM hy b.val).mpr hb,
    ((q.induce S hqS).map j).reachable⟩

/-- The finite mixed-RSW bound survives removal of all unseeded pockets
from the actual band. All attachment geometry, event restriction and exact
FK marginal identities are proved. -/
theorem slit_band_pockets_wiredArc_lower_bound
    (q : Set.Ici (1 : ℝ)) {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M:ℤ)) :
    let H := rankedBandGraph (graph M x y) (D.rank hM hy)
    let S := slitBandPocketCarrier D hM hy
    1/(1+(q:ℝ)^2) ≤
      (measure (H.induce S) (criticalParameters q)
        (isolatedExtensionPullbackBoundary (pocketInclusion S) (rankedBandBoundary (D.rank hM hy)))
        (arcsConnectionEvent (H.induce S) {u | D.rank hM hy u.val.val = 1} {v | D.rank hM hy v.val.val = 3})).toReal := by
  let H := rankedBandGraph (graph M x y) (D.rank hM hy)
  let S := slitBandPocketCarrier D hM hy
  let r := embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S) (pocketInduced_map_le H S)
  let F := arcsConnectionEvent (H.induce S) {u | D.rank hM hy u.val.val = 1} {v | D.rank hM hy v.val.val = 3}
  have hmap := slit_band_pockets_law_map D hM hy (criticalParameters q)
  have hm := congrArg (fun ρ : PMF (Configuration (H.induce S)) => ρ.toMeasure F) hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hm
  have hle : (measure H (criticalParameters q) (rankedBandBoundary (D.rank hM hy))
      (arcsConnectionEvent H (rankedBandFirstArc (D.rank hM hy)) (rankedBandSecondArc (D.rank hM hy)))) ≤
      (law H (criticalParameters q) (rankedBandBoundary (D.rank hM hy))).toMeasure (r ⁻¹' F) := by
    apply MeasureTheory.measure_mono
    exact fun C hC => slit_band_pockets_connection_restricts D hM hy C hC
  have hb := D.wiredArc_lower_bound hM hy q hyM
  have hle' := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hle
  rw [hm] at hle'
  have hb' : 1/(1+(q:ℝ)^2) ≤
      (measure H (criticalParameters q) (rankedBandBoundary (D.rank hM hy))
        (arcsConnectionEvent H (rankedBandFirstArc (D.rank hM hy)) (rankedBandSecondArc (D.rank hM hy)))).toReal := by
    simpa only [rankedBandFirstArc,rankedBandSecondArc,D.rank_first_iff,D.rank_second_iff] using hb
  exact hb'.trans hle' 

end
end PottsContinuity.Push
