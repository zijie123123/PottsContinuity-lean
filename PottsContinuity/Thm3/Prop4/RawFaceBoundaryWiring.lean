module

public import PottsContinuity.Thm3.Prop4.RawFaceBoundaryRetained

/-! # Actual recorded wiring of each raw unreached face-component boundary -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Every adjacency of an unreached face-component boundary has both original
primal endpoints inside the sampled rectangle. -/
theorem rawUnreachedFace_boundary_adj_endpoints (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u v A)ᶜ).ConnectedComponent)
    {x y : LatticeVertex}
    (hxy : (latticeCellBoundaryGraph (rawUnreachedFaceCells a w h u v A C)).Adj x y) :
    x ∈ PD.FK.latticeRectangle a w h ∧ y ∈ PD.FK.latticeRectangle a w h := by
  obtain ⟨_,b,hpair,hlabels⟩ := (latticeCellBoundaryGraph_adj_iff _ _ _).mp hxy
  have hbounds := rawUnreachedFace_boundary_bond_endpoints a w h u v A C b (Ne.symm hlabels)
  rcases Sym2.eq_iff.mp hpair with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact ⟨hs ▸ hbounds.1,ht ▸ hbounds.2⟩
  · exact ⟨ht ▸ hbounds.2,hs ▸ hbounds.1⟩

/-- The actual cell boundary, on its original rectangle carrier, is a
subgraph of the actual RAW recorded-open graph. -/
theorem rawUnreachedFace_boundaryGraph_le_recorded (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).ConnectedComponent) :
    (latticeCellBoundaryGraph (rawUnreachedFaceCells a w h u.val v.val A C)).induce
        (PD.FK.latticeRectangle a w h : Set LatticeVertex) ≤
      openGraph (rectangleGraph a w h)
        (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val := by
  classical
  intro x y hxy
  obtain ⟨_,b,hpair,hlabels⟩ := (latticeCellBoundaryGraph_adj_iff _ _ _).mp hxy
  have hbounds := rawUnreachedFace_boundary_bond_endpoints a w h u.val v.val A C b (Ne.symm hlabels)
  let e : (rectangleGraph a w h).edgeSet := rectanglePrimalBondToEdge a w h ⟨b,hbounds⟩
  have heBond : rectanglePrimalEdgeBond a w h e = b :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨b,hbounds⟩)
  have heFaces : ((rectangleCrossingDualBond a w h e).source ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
      ((rectangleCrossingDualBond a w h e).target ∈ rawUnreachedFaceCells a w h u.val v.val A C) := by
    rw [rectangleCrossingDualBond,heBond,dualBondOfPrimal_source,dualBondOfPrimal_target]
    exact Ne.symm hlabels
  obtain ⟨heA,heR⟩ := rawUnreachedFace_boundary_edge_open_and_revealed a w h u v A C e heFaces
  have hstate : (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val =
      A ∩ sourceMarkedRawReveal a w h u v A := by
    ext f
    simp only [Exploration.revealRecordConfiguration,Finset.mem_inter]
  have heState : e ∈ (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val := by
    rw [hstate]
    exact Finset.mem_inter.mpr ⟨heA,heR⟩
  apply (openGraph_adj _ _ x y).mpr
  refine ⟨e,heState,?_⟩
  apply Sym2.map.injective Subtype.val_injective
  change b.toSym2 = s(x.val,y.val)
  exact hpair

/-- Every two boundary-bond vertices of a raw unexplored FACE component
are actually connected by the SAME raw recorded open original bonds. -/
theorem rawUnreachedFace_boundary_vertices_recorded_connected (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (C : (squareLattice.induce (rawExploredExterior a w h u.val v.val A)ᶜ).ConnectedComponent)
    (b c : LatticeBond)
    (hb : (b.faceBase false ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
      (b.faceBase true ∈ rawUnreachedFaceCells a w h u.val v.val A C))
    (hc : (c.faceBase false ∈ rawUnreachedFaceCells a w h u.val v.val A C) ≠
      (c.faceBase true ∈ rawUnreachedFaceCells a w h u.val v.val A C))
    (x y : RectangleVertex a w h) (hx : x.val ∈ b.toSym2) (hy : y.val ∈ c.toSym2) :
    ActualConnected (rectangleGraph a w h)
      (Exploration.revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val x y := by
  obtain ⟨p⟩ := rawUnreachedFace_boundary_vertices_connected a w h u.val v.val A C b c hb hc x.val y.val hx hy
  have support {s t : LatticeVertex}
      (q : (latticeCellBoundaryGraph (rawUnreachedFaceCells a w h u.val v.val A C)).Walk s t)
      (hs : s ∈ PD.FK.latticeRectangle a w h) :
      ∀ z ∈ q.support, z ∈ PD.FK.latticeRectangle a w h := by
    induction q with
    | nil =>
      intro z hz
      exact (List.mem_singleton.mp hz) ▸ hs
    | cons hst q ih =>
      intro z hz
      rw [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hs
      · exact ih (rawUnreachedFace_boundary_adj_endpoints a w h u.val v.val A C hst).2 z hz
  exact ⟨(p.induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) (support p x.property)).mapLe
    (rawUnreachedFace_boundaryGraph_le_recorded a w h u v A C)⟩

end
end PottsContinuity.Thm3.Prop4
