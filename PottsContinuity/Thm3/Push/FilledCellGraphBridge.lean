module

public import PottsContinuity.Thm3.Push.FilledFaceCells
public import PottsContinuity.PD.FK.EdgeRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- On original rectangle vertices the filled frontier is precisely the
literal cell-boundary graph. Both directions retain original sampled edges. -/
theorem filledTopFrontier_adj_iff_cellBoundary (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (u v : RectangleVertex a w h) :
    (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj u.val v.val ↔
      (openGraph (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A)).Adj u v := by
  classical
  constructor
  · rintro ⟨hbase,b,hb,hpair⟩
    have huv := (rectangleGraph_adj_iff a w h u v).mpr hbase
    let f : (rectangleGraph a w h).edgeSet := ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    have hbond : rectanglePrimalEdgeBond a w h f = b := by
      apply LatticeBond.toSym2_injective
      erw [rectanglePrimalEdgeBond_toSym2_public]
      rw [hpair]
      rfl
    have hf : f ∈ rectangleFilledTopFrontier a w h A := by
      apply (mem_filledTopFrontier_iff_cellBoundary a w h A f).mpr
      simpa only [hbond] using hb
    rw [openGraph_adj]
    exact ⟨f,hf,rfl⟩
  · intro hopen
    have huv := openGraph_le (rectangleGraph a w h) _ hopen
    let f : (rectangleGraph a w h).edgeSet := ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    have hf : f ∈ rectangleFilledTopFrontier a w h A :=
      (coe_mem_openEdges_iff _ _ f).mp ((openGraph_adj _ _ u v).mp hopen)
    have hb := (mem_filledTopFrontier_iff_cellBoundary a w h A f).mp hf
    refine ⟨(rectangleGraph_adj_iff a w h u v).mp huv,
      rectanglePrimalEdgeBond a w h f,hb,?_⟩
    erw [rectanglePrimalEdgeBond_toSym2_public]
    rfl

end
end PottsContinuity.Push
