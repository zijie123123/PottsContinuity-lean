module

public import PottsContinuity.Thm3.Push.BottomCoreAmbientLaw
public import PottsContinuity.Thm3.Push.RectangleThreeSideBonds

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.Square
noncomputable section
local instance bottomCoreMissingEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph (a.1-1,a.2) (w+1) h).edgeSet := Classical.decEq _

/-- For positive primal width, every missing ordinary-rectangle bond lies
internally in one separate side, rather than merely in their common wired
class. This is the stronger geometry needed by actual crossing erasure. -/
theorem bottomCoreAmbient_missing_bond_in_threeSideBonds
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w)
    (u v : RectangleVertex (a.1-1,a.2) (w+1) h)
    (huv : (rectangleGraph (a.1-1,a.2) (w+1) h).Adj u v)
    (he : (⟨s(u,v),(rectangleGraph _ _ _).mem_edgeSet.mpr huv⟩ :
      (rectangleGraph (a.1-1,a.2) (w+1) h).edgeSet) ∈
      subgraphRemovedEdges ((generalRectangleDualBottomCoreGraph a w h).map
        (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding)
        (rectangleGraph (a.1-1,a.2) (w+1) h)) :
    (⟨s(u,v),(rectangleGraph _ _ _).mem_edgeSet.mpr huv⟩ :
      (rectangleGraph (a.1-1,a.2) (w+1) h).edgeSet) ∈
      rectangleThreeSideBonds (a.1-1,a.2) (w+1) h := by
  have hwire := bottomCoreAmbient_removed_edges_wired a w h u v huv he
  rw [BoundaryCondition.wired_rel] at hwire
  rcases hwire with heq | ⟨hu,hv⟩
  · exact (huv.ne heq).elim
  · apply (mem_rectangleThreeSideBonds_pair _ _ _ u v huv).mpr
    have hub := (mem_latticeRectangle _ u.val _ _).mp u.property
    have hvb := (mem_latticeRectangle _ v.val _ _).mp v.property
    have hd : |u.val.1-v.val.1|+|u.val.2-v.val.2| = 1 := huv
    simp only [abs_eq_max_neg] at hd
    simp only [Set.mem_ofPred_eq] at hu hv
    simp only [Nat.cast_add,Nat.cast_one] at hub hvb ⊢
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> omega

end
end PottsContinuity.Push
