module

public import PottsContinuity.Thm3.Prop4.MarkedLowerFaceCells

/-! # Actual sampled frontiers are the restricted finite cell boundaries -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Adding the two unused corner cells changes no original frontier bond. -/
theorem rawFaceRegionFrontier_mem_iff_marked_cell_boundary
    (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop)
    (e : (rectangleGraph a w h).edgeSet) :
    e ∈ rawFaceRegionFrontier a w h P ↔
      rectanglePrimalEdgeBond a w h e ∈ latticeCellBoundaryBonds (markedLowerFaceCells a w h P) := by
  classical
  have hb := rectanglePrimalEdgeBond_endpoints_mem_public a w h e
  have h₀ := markedLowerFaceCells_bond_face_iff a w h P (rectanglePrimalEdgeBond a w h e) hb false
  have h₁ := markedLowerFaceCells_bond_face_iff a w h P (rectanglePrimalEdgeBond a w h e) hb true
  simp only [rawFaceRegionFrontier,Finset.mem_filter,Finset.mem_univ,true_and,
    rectangleCrossingDualBond,dualBondOfPrimal_source,dualBondOfPrimal_target,
    mem_latticeCellBoundaryBonds]
  constructor
  · intro hne heq
    exact hne (propext (h₀.symm.trans ((Iff.of_eq heq).symm.trans h₁)))
  · intro hne heq
    exact hne (propext (h₁.trans ((Iff.of_eq heq).symm.trans h₀.symm)))

/-- The whole original rectangle frontier graph is exactly the induced
finite cell boundary, with actual original vertex and bond carriers. -/
theorem rawFaceRegionFrontier_adj_iff_marked_cell_boundary
    (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop)
    (u v : RectangleVertex a w h) :
    (latticeCellBoundaryGraph (markedLowerFaceCells a w h P)).Adj u.val v.val ↔
      (openGraph (rectangleGraph a w h) (rawFaceRegionFrontier a w h P)).Adj u v := by
  classical
  constructor
  · rintro ⟨hbase,b,hb,hpair⟩
    have huv := (rectangleGraph_adj_iff a w h u v).mpr hbase
    let e : (rectangleGraph a w h).edgeSet := ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    have hbond : rectanglePrimalEdgeBond a w h e = b := by
      apply LatticeBond.toSym2_injective
      erw [rectanglePrimalEdgeBond_toSym2_public]
      rw [hpair]
      rfl
    have he : e ∈ rawFaceRegionFrontier a w h P := by
      apply (rawFaceRegionFrontier_mem_iff_marked_cell_boundary a w h P e).mpr
      simpa only [hbond] using hb
    exact (openGraph_adj _ _ u v).mpr ⟨e,he,rfl⟩
  · intro hopen
    have huv := openGraph_le (rectangleGraph a w h) _ hopen
    let e : (rectangleGraph a w h).edgeSet := ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    have he : e ∈ rawFaceRegionFrontier a w h P :=
      (coe_mem_openEdges_iff _ _ e).mp ((openGraph_adj _ _ u v).mp hopen)
    have hb := (rawFaceRegionFrontier_mem_iff_marked_cell_boundary a w h P e).mp he
    refine ⟨(rectangleGraph_adj_iff a w h u v).mp huv,rectanglePrimalEdgeBond a w h e,hb,?_⟩
    erw [rectanglePrimalEdgeBond_toSym2_public]
    rfl

end
end PottsContinuity.Thm3.Prop4
