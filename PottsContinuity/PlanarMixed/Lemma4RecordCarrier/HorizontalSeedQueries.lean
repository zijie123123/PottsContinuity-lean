module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.InteriorOriginalEdges
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.OriginalQueryPorts

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

/-- A vertical original edge crossing a horizontal rectangle row is represented
also at the top and bottom rows, where no interior-vertex argument applies. -/
theorem original_vertical_edge_represented_at_row
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1+1 ≤ x ∧ x ≤ a.1+(w:ℤ))
    (hy : a.2 ≤ y ∧ y ≤ a.2+(h:ℤ))
    (e : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (he : frozenEdgeEmbedding V e=latticeBondEdge ⟨(x,y),LatticeAxis.vertical⟩) :
    ∃ f : (rectangleGraph a w h).edgeSet,
      rectangleDualOriginalEdge V a w h f=some e := by
  let b : LatticeBond := ⟨(x,y),LatticeAxis.vertical⟩
  have hm : (dualBondOfPrimal b).source ∈ PD.FK.latticeRectangle a w h ∧
      (dualBondOfPrimal b).target ∈ PD.FK.latticeRectangle a w h := by
    simp only [b,dualBondOfPrimal,LatticeBond.source,LatticeBond.target,PD.FK.mem_latticeRectangle]
    omega
  let f := rectanglePrimalBondToEdge a w h ⟨dualBondOfPrimal b,hm⟩
  have hf : rectanglePrimalEdgeBond a w h f=dualBondOfPrimal b :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨dualBondOfPrimal b,hm⟩)
  refine ⟨f,?_⟩
  apply (originalEdgeOfBond_eq_some_iff V _ e).mpr
  rwa [hf,primalBondOfDual_dualBondOfPrimal]

/-- A represented original bond incident to an auxiliary seed is always queried,
regardless of its state or whether the selected crossing uses it. -/
theorem complementary_raw_query_of_original_seed_endpoint
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    (e : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (f : (rectangleGraph a w h).edgeSet)
    (hf : rectangleDualOriginalEdge V a w h f=some e)
    (u : LatticeVertex) (hu : u ∈ Sym2.map Subtype.val e.val)
    (hseed : ∀ v : RectangleDualVertex a w h, faceIndexMark v.val=u → v ∈ seeds) :
    e ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A)) := by
  rw [← rectangle_auxiliary_pair_of_original_edge V a w h f e hf] at hu
  obtain ⟨v,hv,hvu⟩ := Sym2.mem_map.mp hu
  apply (mem_complementaryRevealPullback _ _ _ _ e).mpr
  refine ⟨f,(mem_closedClusterReveal_iff_endpoint _ _ _ f).mpr ⟨v,hv,?_⟩,hf⟩
  exact ⟨v,hseed v hvu,SimpleGraph.Reachable.rfl⟩

/-- The complete upper horizontal seed row is queried, including closed bonds. -/
theorem top_raw_query_contains_vertical_boundary_bond
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (x : ℤ) (hx : a.1+1 ≤ x ∧ x ≤ a.1+(w:ℤ))
    (e : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (he : frozenEdgeEmbedding V e=
      latticeBondEdge ⟨(x,a.2+(h:ℤ)),LatticeAxis.vertical⟩) :
    e ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (rectangleTopReveal a w h (originalClosedDualRectangleRead V a w h A)) := by
  obtain ⟨f,hf⟩ := original_vertical_edge_represented_at_row V a w h x _ hx ⟨by omega,le_rfl⟩ e he
  apply complementary_raw_query_of_original_seed_endpoint V a w h A _ e f hf (x,a.2+(h:ℤ)+1)
  · have hep : Sym2.map Subtype.val e.val =
        (⟨(x,a.2+(h:ℤ)),LatticeAxis.vertical⟩ : LatticeBond).toSym2 := congrArg Subtype.val he
    rw [hep]
    exact Sym2.mem_mk_right _ _
  · intro v hv
    have hxx := congrArg Prod.fst hv
    have hyy := congrArg Prod.snd hv
    simp only [faceIndexMark] at hxx hyy
    apply (rectangleDualTopPorts_mem_iff_coordinates a w h v).mpr
    exact ⟨by omega,by omega,by omega⟩

/-- The complete lower horizontal seed row is queried as well. -/
theorem bottom_raw_query_contains_vertical_boundary_bond
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (x : ℤ) (hx : a.1+1 ≤ x ∧ x ≤ a.1+(w:ℤ))
    (e : (squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (he : frozenEdgeEmbedding V e=latticeBondEdge ⟨(x,a.2),LatticeAxis.vertical⟩) :
    e ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h)
        (rectangleDualBottomPorts a w h) (originalClosedDualRectangleRead V a w h A)) := by
  obtain ⟨f,hf⟩ := original_vertical_edge_represented_at_row V a w h x _ hx ⟨le_rfl,by omega⟩ e he
  apply complementary_raw_query_of_original_seed_endpoint V a w h A _ e f hf (x,a.2)
  · have hep : Sym2.map Subtype.val e.val =
        (⟨(x,a.2),LatticeAxis.vertical⟩ : LatticeBond).toSym2 := congrArg Subtype.val he
    rw [hep]
    exact Sym2.mem_mk_left _ _
  · intro v hv
    have hxx := congrArg Prod.fst hv
    have hyy := congrArg Prod.snd hv
    simp only [faceIndexMark] at hxx hyy
    apply (rectangleDualBottomPorts_mem_iff_coordinates a w h v).mpr
    exact ⟨by omega,by omega,by omega⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
