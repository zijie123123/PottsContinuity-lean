module

public import PottsContinuity.Thm3.RSW.RectangleSubgraphDualEdges
public import PottsContinuity.Thm3.RSW.FiniteDualClosure

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite DualityExt

/-- The finite rectangle's original primal bond has exactly its sampled state
in the whole-plane closed extension, with no exterior bond substituted. -/
theorem rectanglePrimalEdgeBond_closedExtension_iff (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (e : (rectangleGraph a w h).edgeSet) :
    latticeConfigurationBondState (finiteSubgraphConfiguration (PD.FK.latticeRectangle a w h) 0 A)
      (rectanglePrimalEdgeBond a w h e) = false ↔ e ∉ A := by
  classical
  have he : latticeBondEdge (rectanglePrimalEdgeBond a w h e) =
      frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e := by
    have hraw : latticeBondEdge (rectanglePrimalEdgeBond a w h e) =
        rectanglePrimalEdgeToSquareEdge a w h e :=
      Equiv.apply_symm_apply wholePlaneBondEdgeEquiv _
    rw [hraw]
    apply Subtype.ext
    rfl
  change decide (latticeBondEdge (rectanglePrimalEdgeBond a w h e) ∈
    A.map (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h))) = false ↔ _
  rw [decide_eq_false_iff_not,he]
  exact not_congr (Finset.mem_map' (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)))

/-- The retained sampled dual edge has the original primal bond's exact two
face bases, before any boundary identification. -/
theorem rectangleSubgraphSourceDualEdge_facePair
    {a : LatticeVertex} {w h : ℕ} {G : SimpleGraph (RectangleVertex a w h)}
    (hG : G ≤ rectangleGraph a w h) (e : G.edgeSet) :
    Sym2.map Subtype.val (rectangleSubgraphSourceDualEdge hG e).val =
      s((rectanglePrimalEdgeBond a w h (subgraphEdgeEmbedding hG e)).faceBase false,
        (rectanglePrimalEdgeBond a w h (subgraphEdgeEmbedding hG e)).faceBase true) := by
  have hp := congrArg
    (fun d : (rectangleDualGraph a w h).edgeSet => Sym2.map Subtype.val d.val)
    (rectangleSubgraphSourceDualEdge_host hG e)
  change Sym2.map Subtype.val (rectangleSubgraphSourceDualEdge hG e).val =
    Sym2.map Subtype.val
      (rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e)).val at hp
  rw [hp]
  change Sym2.map Subtype.val (rectangleDualCarrierPair a w h
    (rectanglePrimalDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e))) = _
  simp only [rectangleDualCarrierPair,Sym2.map_mk,
    rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
  rfl

/-- Every native sampled dual step replays as an actual closed-dual step of
the original closed host extension, with exactly the same face coordinates. -/
def rectangleSubgraphDualClosedExtensionHom
    {a : LatticeVertex} {w h : ℕ} {G : SimpleGraph (RectangleVertex a w h)}
    (hG : G ≤ rectangleGraph a w h) (A : Configuration G) :
    openGraph (rectangleSubgraphDualGraph hG) (rectangleSubgraphDualConfigurationEquiv hG A) →g
      wholePlaneClosedDualGraph (finiteSubgraphConfiguration (PD.FK.latticeRectangle a w h) 0
        (subgraphConfigurationEmbedding hG A)) where
  toFun := Subtype.val
  map_rel' := by
    intro u v hxy
    rw [openGraph_adj] at hxy
    obtain ⟨d,hd,hpair⟩ := hxy
    let e := (rectangleSubgraphSourceDualEdgeEquiv hG).symm d
    have hed : rectangleSubgraphSourceDualEdge hG e = d :=
      (rectangleSubgraphSourceDualEdgeEquiv hG).apply_symm_apply d
    have heclosed : e ∉ A := (rectangleSubgraphSourceDualEdge_mem hG A e).mp (hed ▸ hd)
    have hhost : subgraphEdgeEmbedding hG e ∉ subgraphConfigurationEmbedding hG A :=
      (not_congr (Finset.mem_map' (subgraphEdgeEmbedding hG))).mpr heclosed
    have hb := (rectanglePrimalEdgeBond_closedExtension_iff a w h
      (subgraphConfigurationEmbedding hG A) (subgraphEdgeEmbedding hG e)).mpr hhost
    have hp := rectangleSubgraphSourceDualEdge_facePair hG e
    rw [hed,hpair] at hp
    change s(u.val,v.val) = _ at hp
    exact ⟨_,hb,Sym2.eq_iff.mp hp⟩

end PottsContinuity.RSW
