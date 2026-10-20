module

public import PottsContinuity.Thm3.Push.BottomCoreMissingSideBonds

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.Square
noncomputable section
local instance coreErasedLiftAmbientEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph (a.1-1,a.2) (w+1) h).edgeSet := Classical.decEq _

/-- The coordinate core map retains each actual sampled core bond. -/
theorem bottomCoreAmbient_map_le (a : LatticeVertex) (w h : ℕ) :
    (generalRectangleDualBottomCoreGraph a w h).map
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding ≤
        rectangleGraph (a.1-1,a.2) (w+1) h := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact generalRectangleDualBottomCoreGraph_le_rectangle a w h hxy

/-- Every sampled step avoiding the three separate removed sides lifts to
an originally open core step in the restricted full sample. -/
theorem bottomCoreAmbient_erased_open_adj_pullback
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w)
    (C : Configuration (rectangleGraph (a.1-1,a.2) (w+1) h))
    (u v : generalRectangleDualBottomCoreVertex a w h)
    (hstep : (openGraph (rectangleGraph (a.1-1,a.2) (w+1) h)
      (C \ rectangleThreeSideBonds (a.1-1,a.2) (w+1) h)).Adj
        (generalRectangleDualBottomCoreVertexEquiv a w h u)
        (generalRectangleDualBottomCoreVertexEquiv a w h v)) :
    (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (embeddedConfigurationRestriction _ _
        (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
        (bottomCoreAmbient_map_le a w h) C)).Adj u v := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1-1,a.2) (w+1) h
  let e := generalRectangleDualBottomCoreVertexEquiv a w h
  let f := e.toEmbedding
  have hadj : H.Adj (e u) (e v) := openGraph_le H _ hstep
  let d : H.edgeSet := ⟨s(e u,e v),H.mem_edgeSet.mpr hadj⟩
  have hd : d ∈ C \ rectangleThreeSideBonds (a.1-1,a.2) (w+1) h :=
    (coe_mem_openEdges_iff H _ d).mp ((openGraph_adj H _ _ _).mp hstep)
  have hG : G.Adj u v := by
    by_contra hnot
    have hnotmap : s(e u,e v) ∉ (G.map f).edgeSet := by
      intro he
      obtain ⟨x,y,hxy,hx,hy⟩ := (SimpleGraph.map_adj _ _ _ _).mp ((G.map f).mem_edgeSet.mp he)
      have hxu : x=u := e.injective hx
      have hyv : y=v := e.injective hy
      subst x
      subst y
      exact hnot hxy
    have hremoved : d ∈ subgraphRemovedEdges (G.map f) H :=
      (mem_subgraphRemovedEdges d).mpr hnotmap
    have hside := bottomCoreAmbient_missing_bond_in_threeSideBonds a w h hw (e u) (e v) hadj hremoved
    exact (Finset.mem_sdiff.mp hd).2 hside
  let dG : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr hG⟩
  apply (openGraph_adj _ _ u v).mpr
  refine ⟨dG,?_,rfl⟩
  apply (mem_embeddedConfigurationRestriction _ _ _ _ C dG).mpr
  have heq : embeddedEdgeEmbedding G H f (bottomCoreAmbient_map_le a w h) dG = d :=
    Subtype.ext rfl
  rw [heq]
  exact (Finset.mem_sdiff.mp hd).1

/-- Map any actual walk avoiding the removed side bonds into the actual
sampled core. The inverse coordinate map preserves its entire ordered trace. -/
def bottomCoreErasedOpenHom (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w)
    (C : Configuration (rectangleGraph (a.1-1,a.2) (w+1) h)) :
    openGraph (rectangleGraph (a.1-1,a.2) (w+1) h)
      (C \ rectangleThreeSideBonds (a.1-1,a.2) (w+1) h) →g
    openGraph (generalRectangleDualBottomCoreGraph a w h)
      (embeddedConfigurationRestriction _ _
        (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
        (bottomCoreAmbient_map_le a w h) C) where
  toFun := (generalRectangleDualBottomCoreVertexEquiv a w h).symm
  map_rel' := by
    intro u v huv
    apply bottomCoreAmbient_erased_open_adj_pullback a w h hw C
    simpa only [Equiv.apply_symm_apply] using huv

end
end PottsContinuity.Push
