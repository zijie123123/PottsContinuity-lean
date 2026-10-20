module

public import PottsContinuity.Thm3.Push.DualBondLocalization
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- If both actual endpoints of a normalized outer bond belong to the inner
rectangle, that bond is the image of its unique inner original edge. -/
theorem rectangle_original_bond_pullback {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (f : (rectangleGraph b W H).edgeSet)
    (hinside : (rectanglePrimalEdgeBond b W H f).source ∈ PD.FK.latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond b W H f).target ∈ PD.FK.latticeRectangle a w h) :
    ∃ e : (rectangleGraph a w h).edgeSet,
      embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
        (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) e = f := by
  let c : RectanglePrimalBond a w h := ⟨rectanglePrimalEdgeBond b W H f,hinside⟩
  let e := (rectanglePrimalEdgeBondEquiv a w h).symm c
  have he : rectanglePrimalEdgeBond a w h e=rectanglePrimalEdgeBond b W H f :=
    congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv a w h).apply_symm_apply c)
  refine ⟨e,?_⟩
  apply (rectanglePrimalEdgeBondEquiv b W H).injective
  apply Subtype.ext
  exact (rectanglePrimalEdgeBond_embedded hrect e).trans he

/-- A closed original bond which lies in the inner rectangle gives its
actual complementary dual step in the RESTRICTED configuration. This is a
step transport on genuine bonds, not an induced-expanded-graph assertion. -/
theorem rectangle_closed_dual_step_pullback {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (A : Configuration (rectangleGraph b W H)) (f : (rectangleGraph b W H).edgeSet)
    (hf : f ∉ A)
    (hinside : (rectanglePrimalEdgeBond b W H f).source ∈ PD.FK.latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond b W H f).target ∈ PD.FK.latticeRectangle a w h)
    (u v : RectangleDualVertex a w h)
    (hpair : s(u.val,v.val)=s((rectanglePrimalEdgeBond b W H f).faceBase false,
      (rectanglePrimalEdgeBond b W H f).faceBase true)) :
    (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h (DualityExt.rectangleConfigurationRestriction hrect A))).Adj u v := by
  obtain ⟨e,he⟩ := rectangle_original_bond_pullback hrect f hinside
  have hn : rectanglePrimalEdgeBond a w h e=rectanglePrimalEdgeBond b W H f := by
    rw [← he,rectanglePrimalEdgeBond_embedded]
  apply rectangle_closed_dual_step_of_original_bond a w h _ e ?_ u v ?_
  · intro heA
    exact hf (he ▸ ((mem_embeddedConfigurationRestriction _ _ _ _ A e).mp heA))
  · simpa only [hn] using hpair

end
end PottsContinuity.Push
