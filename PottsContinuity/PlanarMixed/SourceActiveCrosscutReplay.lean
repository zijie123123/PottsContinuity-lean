module

public import PottsContinuity.PlanarMixed.SourceActiveCrosscutComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section
local instance activeReplayEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A sampled residual edge remains sampled under its original host embedding. -/
def embeddedSampleOpenHom {U V : Type*}
    (H : SimpleGraph U) (J : SimpleGraph V) (i : U ↪ V) (h : H.map i ≤ J)
    (C : Configuration H) : openGraph H C →g
      openGraph J (embeddedConfigurationEmbedding H J i h C) where
  toFun := i
  map_rel' := by
    intro u v huv
    change (openGraph J (subgraphConfigurationEmbedding h
      (isolatedExtensionConfigurationEquiv H i C))).Adj (i u) (i v)
    rw [openGraph_subgraphConfigurationEmbedding,openGraph_isolatedExtension]
    exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,huv,rfl,rfl⟩

namespace HorizontalSquareCrosscutData
variable {a : LatticeVertex} {N : ℕ} (D : HorizontalSquareCrosscutData a N)

/-- Pointwise G2 surgery from the actual residual graph into the original
host, restoring only recorded paths. The residual graph need not contain any
exposed path bond or the full reference square. -/
theorem active_residual_restored_starts_connected
    {U V : Type*} [Finite U] [Finite V]
    (H : SimpleGraph U) (J : SimpleGraph V)
    (e : U ↪ V) (hHJ : H.map e ≤ J)
    (i : RectangleVertex a N N ↪ V) (hSquare : (rectangleGraph a N N).map i ≤ J)
    (f : rankedBandVertices D.rank ↪ U)
    (hBand : (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
      (bandArcBonds _ D.rank)).map f ≤ H)
    (hcoords : ∀ v, e (f v) = i v.val)
    (K : Configuration J)
    (hstate : D.state = embeddedConfigurationRestriction (rectangleGraph a N N) J i hSquare K)
    (C : Configuration H)
    (hconn : embeddedConfigurationRestriction
      (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
        (bandArcBonds _ D.rank)) H f hBand C ∈
        arcsConnectionEvent _ {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support}) :
    ActualConnected (rectangleGraph a N N)
      (embeddedConfigurationRestriction (rectangleGraph a N N) J i hSquare
        (embeddedConfigurationEmbedding H J e hHJ C ∪ K)) D.firstStart D.secondStart := by
  obtain ⟨u,hu,v,hv,⟨p⟩⟩ := hconn
  let L := embeddedConfigurationEmbedding H J e hHJ C ∪ K
  let mid : openGraph
      (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
        (bandArcBonds _ D.rank)) (embeddedConfigurationRestriction _ H f hBand C) →g
      openGraph (rectangleGraph a N N)
        (embeddedConfigurationRestriction (rectangleGraph a N N) J i hSquare L) :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        have hs := (embeddedRestriction_openGraph_adj_iff _ H f hBand C x y).mp hxy
        have hhost := (embeddedSampleOpenHom H J e hHJ C).map_rel hs.2
        change (openGraph J (embeddedConfigurationEmbedding H J e hHJ C)).Adj
          (e (f x)) (e (f y)) at hhost
        rw [hcoords x,hcoords y] at hhost
        apply (embeddedRestriction_openGraph_adj_iff _ J i hSquare L x.val y.val).mpr
        have hsource : (rectangleGraph a N N).Adj x.val y.val :=
          edgeRestriction_le (rankedBandGraph (rectangleGraph a N N) D.rank)
            (bandArcBonds _ D.rank) hs.1
        exact ⟨hsource,
          openGraph_mono (show embeddedConfigurationEmbedding H J e hHJ C ⊆ L
            from Finset.subset_union_left) hhost⟩ }
  have hmiddle : ActualConnected (rectangleGraph a N N)
      (embeddedConfigurationRestriction (rectangleGraph a N N) J i hSquare L) u.val v.val :=
    ⟨p.map mid⟩
  have hfirst := openWalk_support_actualConnected _ D.state D.first D.first.start_mem_support hu
  have hsecond := openWalk_support_actualConnected _ D.state D.second hv D.second.start_mem_support
  rw [hstate] at hfirst hsecond
  have hK := embeddedConfigurationRestriction_monotone (rectangleGraph a N N) J i hSquare
    (show K ⊆ L from Finset.subset_union_right)
  exact (actualConnected_mono hK hfirst).trans
    (hmiddle.trans (actualConnected_mono hK hsecond))

end HorizontalSquareCrosscutData
end
end PottsContinuity.PlanarMixed
