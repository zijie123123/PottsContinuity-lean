module

public import PottsContinuity.Thm3.RSW.StripCentralPrunedEmbedding

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PD.FK.Medial DualityExt
noncomputable section

/-- The physical dual bond of a local rectangle edge depends only on its
original primal bond label, independently of the surrounding rectangle. -/
theorem rectangleDualEdgeEquiv_physical_pair (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    Sym2.map (fun z : RectangleDualVertex a w h => z.val)
      (rectangleDualEdgeEquiv a w h e).val =
      (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e)).toSym2 := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  change s((rectangleDualEdgeSource a w h d).val,
    (rectangleDualEdgeTarget a w h d).val)=_
  rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
  simp [d,rectanglePrimalDualEdgeEquiv,LatticeBond.toSym2,
    dualBondOfPrimal_source,dualBondOfPrimal_target]

/-- The global retained dual edge has exactly the local dual edge's physical
unordered endpoints. No endpoint is shifted, clipped or replaced. -/
theorem stripCentralRetainedDualEdge_physical_pair (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (e : (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet) :
    Sym2.map (fun z : RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) => z.val)
      (stripCentralRetainedDualEdge n k M hn hM e).val =
    Sym2.map (fun z : RectangleDualVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) => z.val)
      (rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n) e).val := by
  rw [stripCentralRetainedDualEdge,rectangleSubgraphDualEdgeEmbedding_crossingBond,
    rectangleDualEdgeEquiv_physical_pair]
  let hostEdge : rectanglePrimalEdgeCarrier (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) :=
    subgraphEdgeEmbedding (stripRectangleWithoutTop_map_le n M)
      (embeddedEdgeEmbedding _ _ (stripCentralPrimalHostEmbedding n k M hM)
        (stripCentralPrimalHost_map_le_pruned n k M hn hM) e)
  change (dualBondOfPrimal (rectanglePrimalEdgeBond _ _ _ hostEdge)).toSym2 =
    (dualBondOfPrimal (rectanglePrimalEdgeBond _ _ _ e)).toSym2
  let localEdge : rectanglePrimalEdgeCarrier (-(k:ℤ)*n,0) (2*k*n) (2*n) := e
  change (dualBondOfPrimal (rectanglePrimalEdgeBond _ _ _ hostEdge)).toSym2 =
    (dualBondOfPrimal (rectanglePrimalEdgeBond _ _ _ localEdge)).toSym2
  have hb : rectanglePrimalEdgeBond _ _ _ hostEdge=rectanglePrimalEdgeBond _ _ _ localEdge := by
    apply LatticeBond.toSym2_injective
    rw [rectanglePrimalEdgeBond_toSym2_public,rectanglePrimalEdgeBond_toSym2_public]
    simp only [hostEdge,subgraphEdgeEmbedding_coe,embeddedEdgeEmbedding_coe,
      Function.Embedding.sym2Map_apply,Sym2.map_map]
    rfl
  rw [hb]

end
end PottsContinuity.RSW
