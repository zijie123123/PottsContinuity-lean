module

public import PottsContinuity.DualityExt.CrossingRestriction
public import PottsContinuity.Thm3.Push.FilledFrontierDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Normalizing a literal original bond is independent of the containing
rectangle. This identifies original edges before transporting any dual label. -/
theorem rectanglePrimalEdgeBond_embedded {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (f : (rectangleGraph a w h).edgeSet) :
    rectanglePrimalEdgeBond b W H
      (embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
        (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) f) =
      rectanglePrimalEdgeBond a w h f := by
  apply LatticeBond.toSym2_injective
  erw [rectanglePrimalEdgeBond_toSym2_public,rectanglePrimalEdgeBond_toSym2_public,
    embeddedEdgeEmbedding_coe]
  change Sym2.map (fun z : RectangleVertex b W H => z.val)
    (Sym2.map (DualityExt.rectangleVertexEmbedding hrect) f.val) =
    Sym2.map (fun z : RectangleVertex a w h => z.val) f.val
  rw [Sym2.map_map]
  rfl

/-- Literal inclusion of expanded true-dual face carriers. -/
def rectangleDualVertexEmbedding {a b : LatticeVertex} {w h W H : ℕ}
    (hdual : rectangleDualExpanded a w h ⊆ rectangleDualExpanded b W H) :
    RectangleDualVertex a w h ↪ RectangleDualVertex b W H where
  toFun v := ⟨v.val,hdual v.property⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun z : RectangleDualVertex b W H => z.val) huv

/-- Both endpoints of the true complementary dual of an original bond
commute with rectangle inclusion, without identifying primal and dual edges. -/
theorem rectangleDualEndpoints_embedded {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (hdual : rectangleDualExpanded a w h ⊆ rectangleDualExpanded b W H)
    (f : (rectangleGraph a w h).edgeSet) :
    let g := embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) f
    let d := rectanglePrimalDualEdgeEquiv a w h f
    let D := rectanglePrimalDualEdgeEquiv b W H g
    rectangleDualVertexEmbedding hdual (rectangleDualEdgeSource a w h d) =
      rectangleDualEdgeSource b W H D ∧
    rectangleDualVertexEmbedding hdual (rectangleDualEdgeTarget a w h d) =
      rectangleDualEdgeTarget b W H D := by
  dsimp only
  constructor
  · apply Subtype.ext
    change (rectangleDualEdgeSource a w h _).val = (rectangleDualEdgeSource b W H _).val
    rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeSource_faceBase]
    exact (congrArg (fun z : LatticeBond => z.faceBase false)
      (rectanglePrimalEdgeBond_embedded hrect f)).symm
  · apply Subtype.ext
    change (rectangleDualEdgeTarget a w h _).val = (rectangleDualEdgeTarget b W H _).val
    rw [rectangleDualEdgeTarget_faceBase,rectangleDualEdgeTarget_faceBase]
    exact (congrArg (fun z : LatticeBond => z.faceBase true)
      (rectanglePrimalEdgeBond_embedded hrect f)).symm

end
end PottsContinuity.Push
