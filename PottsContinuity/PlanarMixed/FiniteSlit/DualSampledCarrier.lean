module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveDualEquiv
public import PottsContinuity.PD.Duality.DualConfigurationBridge

/-! The exact sampled dual graph after conditioning the balanced rectangle.
Every remaining rectangle crossing edge is one reflected active source edge. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section

/-- Literal edge inclusion along the finite reflected cell embedding. -/
def dualHostEdgeEmbedding (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) :
    (dualGraph M x y).edgeSet ↪
      (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet :=
  embeddedEdgeEmbedding _ _ (cellEmbedding M x hM) (dualGraph_map_le_rectangleDual M x y hM)

/-- The sampled edge map is exactly the original rectangle crossing map. -/
theorem dualHostEdgeEmbedding_eq_crossing (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (e : (activeGraph M x y).edgeSet) :
    rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
      (subgraphEdgeEmbedding (activeGraph_le_rectangle M x y) e) =
    dualHostEdgeEmbedding M x y hM (activeCrossingEdgeEquiv M x y hM hy hyM e) := by
  obtain ⟨b,rfl⟩ := (normalizedActiveEdgeEquiv M x y).surjective e
  simp only [activeCrossingEdgeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
  apply (rectangleDualEdgeToSquareEdge _ _ _).injective
  have hprimal : rectanglePrimalEdgeToSquareEdge (x-(M : ℤ),0) (2*M-1) M
      (subgraphEdgeEmbedding (activeGraph_le_rectangle M x y)
        (normalizedActiveEdgeEquiv M x y b)) = latticeBondEdge b.val := Subtype.ext rfl
  change rectangleDualEdgeToSquareEdge _ _ _
    (rectangleDualGraphEdgeEquiv _ _ _ (rectanglePrimalDualEdgeEquiv _ _ _ _)) = _
  rw [rectangleDualEdgeToSquareEdge_carrier]
  change latticeBondEdge (dualBondOfPrimal (wholePlaneBondEdgeEquiv.symm
    (rectanglePrimalEdgeToSquareEdge _ _ _ _))) = _
  rw [hprimal]
  have hb : wholePlaneBondEdgeEquiv.symm (latticeBondEdge b.val) = b.val :=
    wholePlaneBondEdgeEquiv.symm_apply_apply _
  rw [hb]
  apply Subtype.ext
  change (dualBondOfPrimal b.val).toSym2 =
    Sym2.map (faceMap x) (slitReflectedBond x b.val).toSym2
  exact crossingBond_faceMap_pair x b.val

/-- The actual dual host with exactly its exterior carrier removed. -/
def dualSampledGraph (M : ℕ) (x y : ℤ) :=
  edgeRestriction (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (dualRemovedEdges M x y)

/-- Literal remaining-carrier membership is original active-edge membership. -/
theorem dualSampledGraph_mem_edge_iff (M : ℕ) (x y : ℤ)
    (e : (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet) :
    e.val ∈ (dualSampledGraph M x y).edgeSet ↔
      ((rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M).symm e).val ∈
        (activeGraph M x y).edgeSet := by
  rw [dualSampledGraph,edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff,e.property,true_and,coe_mem_openEdges_iff,
    dualRemovedEdges,rectangleSubgraphRemovedDualEdges,
    Finset.mem_map_equiv,mem_subgraphRemovedEdges,not_not]

/-- The remaining dual host graph is exactly the embedded actual reflected
sampled graph. All host vertices outside its image are isolated. -/
theorem dualSampledGraph_eq_map (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    dualSampledGraph M x y = (dualGraph M x y).map (cellEmbedding M x hM) := by
  let D := dualGraph M x y
  let f := cellEmbedding M x hM
  let d := rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
  let J := activeCrossingEdgeEquiv M x y hM hy hyM
  let I := isolatedExtensionEdgeEquiv D f
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro huv
    have hhost := edgeRestriction_le _ (dualRemovedEdges M x y) huv
    let e : (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet :=
      ⟨s(u,v),(rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M).mem_edgeSet.mpr hhost⟩
    have he := (dualSampledGraph_mem_edge_iff M x y e).mp
      ((dualSampledGraph M x y).mem_edgeSet.mpr huv)
    let a : (activeGraph M x y).edgeSet := ⟨(d.symm e).val,he⟩
    have ha := dualHostEdgeEmbedding_eq_crossing M x y hM hy hyM a
    have ht : subgraphEdgeEmbedding (activeGraph_le_rectangle M x y) a = d.symm e :=
      Subtype.ext rfl
    change d (subgraphEdgeEmbedding _ a) = dualHostEdgeEmbedding M x y hM (J a) at ha
    rw [ht,d.apply_symm_apply] at ha
    apply (D.map f).mem_edgeSet.mp
    change e.val ∈ (D.map f).edgeSet
    rw [ha]
    exact (I (J a)).property
  · intro huv
    let e : (D.map f).edgeSet := ⟨s(u,v),(D.map f).mem_edgeSet.mpr huv⟩
    let t := I.symm e
    let a := J.symm t
    have hpair : (dualHostEdgeEmbedding M x y hM t).val = s(u,v) :=
      congrArg Subtype.val (I.apply_symm_apply e)
    apply (dualSampledGraph M x y).mem_edgeSet.mp
    rw [← hpair]
    apply (dualSampledGraph_mem_edge_iff M x y _).mpr
    have ha := dualHostEdgeEmbedding_eq_crossing M x y hM hy hyM a
    have hJ : J a = t := J.apply_symm_apply t
    change d (subgraphEdgeEmbedding _ a) = dualHostEdgeEmbedding M x y hM (J a) at ha
    rw [hJ] at ha
    rw [← ha]
    change (d.symm (d (subgraphEdgeEmbedding _ a))).val ∈ _
    rw [d.symm_apply_apply]
    exact a.property

end
end PottsContinuity.PlanarMixed.FiniteSlit
