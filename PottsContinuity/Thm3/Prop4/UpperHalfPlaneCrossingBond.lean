module

public import PottsContinuity.Thm3.Prop4.RectangleFrozenDuality
public import PottsContinuity.Thm3.Prop4.TiltedWindow

/-!
# Genuine crossed bonds above a supporting line

The two dual face labels are the lower-left corners of their physical cells.
Their nonnegative heights force an endpoint of the crossed original bond
strictly above the line, including the two endpoint slopes.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Every actual original bond with both adjacent face labels above the line
has an original endpoint strictly above it. No slope restriction is needed. -/
theorem primal_endpoint_above_of_face_heights (e : LatticeBond) (t c : ℝ)
    (hfalse : c ≤ tiltedHeight t (e.faceBase false))
    (htrue : c ≤ tiltedHeight t (e.faceBase true)) :
    c < tiltedHeight t e.source ∨ c < tiltedHeight t e.target := by
  rcases e with ⟨⟨x,y⟩,axis⟩
  cases axis
  · left
    simp only [LatticeBond.faceBase, LatticeBond.source, tiltedHeight,
      Int.cast_sub, Int.cast_one] at hfalse ⊢
    linarith only [hfalse]
  · right
    simp only [LatticeBond.faceBase, LatticeBond.target, tiltedHeight,
      Int.cast_add, Int.cast_one] at htrue ⊢
    linarith only [htrue]

/-- Revealing only original bonds below a line leaves every genuine dual bond
whose two face labels lie above that line available for the dual reference law. -/
theorem upper_face_dual_edge_not_crossed (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (t c : ℝ)
    (hR : ∀ e ∈ R, tiltedHeight t (rectanglePrimalEdgeBond a w h e).source ≤ c ∧
      tiltedHeight t (rectanglePrimalEdgeBond a w h e).target ≤ c)
    (d : RectangleDualEdgeCarrier a w h)
    (hs : c ≤ tiltedHeight t d.crossingBond.source)
    (ht : c ≤ tiltedHeight t d.crossingBond.target) :
    rectangleDualGraphEdgeEquiv a w h d ∉ rectangleCrossedEdges a w h R := by
  classical
  intro hd
  change rectangleDualGraphEdgeEquiv a w h d ∈
    R.map (rectangleCrossingEdgeEquiv a w h).toEmbedding at hd
  rw [Finset.mem_map_equiv] at hd
  change (rectanglePrimalDualEdgeEquiv a w h).symm
    ((rectangleDualGraphEdgeEquiv a w h).symm (rectangleDualGraphEdgeEquiv a w h d)) ∈ R at hd
  rw [Equiv.symm_apply_apply] at hd
  have hd' : d.primalEdge ∈ R := hd
  have hends := hR d.primalEdge hd'
  have h0 := rectangleDualEdgeSource_faceBase a w h d
  have h1 := rectangleDualEdgeTarget_faceBase a w h d
  change d.crossingBond.source = _ at h0
  change d.crossingBond.target = _ at h1
  rw [h0] at hs
  rw [h1] at ht
  rcases primal_endpoint_above_of_face_heights _ t c hs ht with he | he
  · exact (not_lt_of_ge hends.1) he
  · exact (not_lt_of_ge hends.2) he

end
end PottsContinuity.Thm3.Prop4
