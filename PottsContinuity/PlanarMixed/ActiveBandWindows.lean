module

public import PottsContinuity.PlanarMixed.SourceActiveCrosscutReplay

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Restrict a GLOBAL cut labelling to a literal subdomain. All pieces of
both original recorded traces are retained in the local marked sets. -/
def bandWindowEmbedding {V W : Type*} (i : V ↪ W) (r : W → ℤ) :
    rankedBandVertices (r ∘ i) ↪ rankedBandVertices r where
  toFun v := ⟨i v.val,v.property⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact i.injective (congrArg Subtype.val huv)

/-- The edge guard restricts along every actual subgraph embedding. -/
theorem bandWindow_rank_edges {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (i : V ↪ W) (hGH : G.map i ≤ H)
    (r : W → ℤ) (hstep : RankedBandEdges H r) : RankedBandEdges G (r ∘ i) := by
  intro u v huv
  exact hstep (i u) (i v) (hGH ((SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,huv,rfl,rfl⟩))

/-- Restricting the global band gives actual active-carrier inclusion.
This uses the global trace labels, rather than labels recomputed from one crop. -/
theorem bandWindow_active_map_le {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (i : V ↪ W) (hGH : G.map i ≤ H)
    (r : W → ℤ) :
    (edgeRestriction (rankedBandGraph G (r ∘ i)) (bandArcBonds G (r ∘ i))).map
      (bandWindowEmbedding i r) ≤
        edgeRestriction (rankedBandGraph H r) (bandArcBonds H r) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  have hG : G.Adj u.val v.val :=
    edgeRestriction_le (rankedBandGraph G (r ∘ i)) (bandArcBonds G (r ∘ i)) huv
  have hH : H.Adj (i u.val) (i v.val) :=
    hGH ((SimpleGraph.map_adj _ _ _ _).mpr ⟨u.val,v.val,hG,rfl,rfl⟩)
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hH,?_⟩
  intro he
  have harc := (coe_mem_openEdges_iff (rankedBandGraph H r) (bandArcBonds H r)
    (⟨s(bandWindowEmbedding i r u,bandWindowEmbedding i r v),
      (rankedBandGraph H r).mem_edgeSet.mpr hH⟩ : (rankedBandGraph H r).edgeSet)).mp he
  have hlabels := (mem_bandArcBonds_pair H r
    (bandWindowEmbedding i r u) (bandWindowEmbedding i r v) hH).mp harc
  have hlocal : (⟨s(u,v),(rankedBandGraph G (r ∘ i)).mem_edgeSet.mpr hG⟩ :
      (rankedBandGraph G (r ∘ i)).edgeSet) ∈ bandArcBonds G (r ∘ i) := by
    apply (mem_bandArcBonds_pair G (r ∘ i) u v hG).mpr
    exact hlabels
  exact (SimpleGraph.deleteEdges_adj.mp huv).2 ((coe_mem_openEdges_iff _ _ _).mpr hlocal)

end
end PottsContinuity.PlanarMixed
