module

public import PottsContinuity.Thm3.Push.SlitCrosscutPocketLaw

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit PlanarMixed.Square
noncomputable section
local instance slitBandPocketEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The original induced band with the unseeded pockets of either cut removed. -/
def slitBandPocketCarrier {M : ℕ} {x y : ℤ} (D : CrosscutData M x y)
    (hM : 2 ≤ M) (hy : 0 < y) : Set (rankedBandVertices (D.rank hM hy)) :=
  {v | v.val ∈ slitCrosscutPocketCarrier D}

private theorem slitBandPocket_free {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) :
    ∀ a b, a ∉ slitBandPocketCarrier D hM hy →
      (rankedBandBoundary (D.rank hM hy)).partition.r a b → a = b := by
  intro a b ha hab
  have hs := slit_crosscuts_cross_seeded_exteriors D hM
  rcases (twoBlockBoundary_partition_rel _ _ _ a b).mp hab with h | h | h
  · exact h
  · have hpa : a.val ∈ D.first.support := (D.rank_first_iff hM hy a.val).mp h.1
    exact False.elim (ha ⟨Or.inr hpa,hs.1 hpa⟩)
  · have hqa : a.val ∈ D.second.support := (D.rank_second_iff hM hy a.val).mp h.1
    exact False.elim (ha ⟨hs.2 hqa,Or.inr hqa⟩)

/-- The actual band geometry discharges the deleted-component no-bridge
condition. The two cut classes are preserved separately. -/
theorem slit_band_pockets_no_bridge {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) :
    ∀ (a b : {v : rankedBandVertices (D.rank hM hy) // v ∉ slitBandPocketCarrier D hM hy}),
      ((rankedBandGraph (graph M x y) (D.rank hM hy)).induce
        (slitBandPocketCarrier D hM hy)ᶜ).Reachable a b →
      ∀ u v : slitBandPocketCarrier D hM hy,
        (rankedBandGraph (graph M x y) (D.rank hM hy)).Adj a.val u.val →
        (rankedBandGraph (graph M x y) (D.rank hM hy)).Adj b.val v.val →
        (rankedBandBoundary (D.rank hM hy)).partition.r u.val v.val := by
  intro a b hab u v hau hbv
  let f : ((rankedBandGraph (graph M x y) (D.rank hM hy)).induce
      (slitBandPocketCarrier D hM hy)ᶜ) →g
      ((graph M x y).induce (slitCrosscutPocketCarrier D)ᶜ) := {
    toFun := fun z => ⟨z.val.val,z.property⟩
    map_rel' := fun h => h }
  have h := slit_crosscuts_pocket_attachments_in_same_cut D hM (f a) (f b) (hab.map f)
    ⟨u.val.val,u.property⟩ ⟨v.val.val,v.property⟩ hau hbv
  rcases h with h | h
  · exact (twoBlockBoundary_partition_rel _ _ _ _ _).mpr (Or.inr (Or.inl
      ⟨(D.rank_first_iff hM hy u.val.val).mpr h.1,(D.rank_first_iff hM hy v.val.val).mpr h.2⟩))
  · exact (twoBlockBoundary_partition_rel _ _ _ _ _).mpr (Or.inr (Or.inr
      ⟨(D.rank_second_iff hM hy u.val.val).mpr h.1,(D.rank_second_iff hM hy v.val.val).mpr h.2⟩))

def slitBandPocket_root {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) : slitBandPocketCarrier D hM hy := by
  have hs := slit_crosscuts_cross_seeded_exteriors D hM
  have hr := (D.rank_first_iff hM hy D.firstStart).mpr D.first.start_mem_support
  exact ⟨⟨D.firstStart,by change 1 ≤ D.rank hM hy D.firstStart ∧ D.rank hM hy D.firstStart ≤ 3; omega⟩,
    Or.inr D.first.start_mem_support,hs.1 D.first.start_mem_support⟩

/-- Removing the unseeded pockets from the actual induced crosscut band
preserves its exact FK marginal for every admissible parameter. -/
theorem slit_band_pockets_law_map {M : ℕ} {x y : ℤ}
    (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y) (θ : Parameters) :
    let H := rankedBandGraph (graph M x y) (D.rank hM hy)
    let S := slitBandPocketCarrier D hM hy
    (law H θ (rankedBandBoundary (D.rank hM hy))).map
      (embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S) (pocketInduced_map_le H S)) =
    law (H.induce S) θ (isolatedExtensionPullbackBoundary (pocketInclusion S)
      (rankedBandBoundary (D.rank hM hy))) := by
  dsimp only
  exact componentPocket_law_map_of_no_bridge _ θ _ _ (slitBandPocket_root D hM hy)
    (slitBandPocket_free D hM hy) (slit_band_pockets_no_bridge D hM hy)

end
end PottsContinuity.Push
