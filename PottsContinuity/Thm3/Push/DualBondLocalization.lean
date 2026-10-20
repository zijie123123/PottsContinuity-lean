module

public import PottsContinuity.Thm3.Push.RectangleCarrierInclusion
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- The actual true-dual endpoint pair of an original edge is exactly the
pair of adjacent normalized faces. No primal/dual carrier identification is
implicit in this bridge. -/
theorem rectangle_dual_edge_face_pair (a : LatticeVertex) (w h : ℕ)
    (f : (rectangleGraph a w h).edgeSet) :
    Sym2.map (fun z : RectangleDualVertex a w h => z.val)
      (DualityExt.rectangleDualEdgeEquiv a w h f).val =
    s((rectanglePrimalEdgeBond a w h f).faceBase false,
      (rectanglePrimalEdgeBond a w h f).faceBase true) := by
  change s((rectangleDualEdgeSource a w h (rectanglePrimalDualEdgeEquiv a w h f)).val,
    (rectangleDualEdgeTarget a w h (rectanglePrimalDualEdgeEquiv a w h f)).val) = _
  rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
  rfl

/-- Each genuine dual step names the unique original crossing bond. -/
theorem rectangle_dual_step_original_bond (a : LatticeVertex) (w h : ℕ)
    {u v : RectangleDualVertex a w h} (huv : (rectangleDualGraph a w h).Adj u v) :
    ∃ f : (rectangleGraph a w h).edgeSet,
      s(u.val,v.val)=s((rectanglePrimalEdgeBond a w h f).faceBase false,
        (rectanglePrimalEdgeBond a w h f).faceBase true) := by
  let e : (rectangleDualGraph a w h).edgeSet := ⟨s(u,v),(rectangleDualGraph a w h).mem_edgeSet.mpr huv⟩
  let f := (DualityExt.rectangleDualEdgeEquiv a w h).symm e
  refine ⟨f,?_⟩
  have he : DualityExt.rectangleDualEdgeEquiv a w h f=e := Equiv.apply_symm_apply _ _
  have hp := rectangle_dual_edge_face_pair a w h f
  rw [he] at hp
  exact hp

/-- Every OPEN complementary-dual step crosses an actually CLOSED original
bond, with both literal face endpoints retained. -/
theorem rectangle_closed_dual_step_original_bond (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleDualVertex a w h}
    (huv : (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v) :
    ∃ f : (rectangleGraph a w h).edgeSet, f ∉ A ∧
      s(u.val,v.val)=s((rectanglePrimalEdgeBond a w h f).faceBase false,
        (rectanglePrimalEdgeBond a w h f).faceBase true) := by
  let e : (rectangleDualGraph a w h).edgeSet :=
    ⟨s(u,v),(rectangleDualGraph a w h).mem_edgeSet.mpr (openGraph_le _ _ huv)⟩
  let f := (DualityExt.rectangleDualEdgeEquiv a w h).symm e
  have he : DualityExt.rectangleDualEdgeEquiv a w h f=e := Equiv.apply_symm_apply _ _
  have heA : e ∈ auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A := by
    rw [auxiliaryClosedConfiguration_rectangle_eq]
    exact (coe_mem_openEdges_iff _ _ e).mp ((openGraph_adj _ _ u v).mp huv)
  refine ⟨f,(mem_auxiliaryClosedConfiguration _ A e).mp heA,?_⟩
  have hp := rectangle_dual_edge_face_pair a w h f
  rw [he] at hp
  exact hp

/-- Conversely, a closed original bond gives its genuine complementary
open dual step whenever the supplied vertices are its two actual faces. -/
theorem rectangle_closed_dual_step_of_original_bond (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (f : (rectangleGraph a w h).edgeSet)
    (hf : f ∉ A) (u v : RectangleDualVertex a w h)
    (hpair : s(u.val,v.val)=s((rectanglePrimalEdgeBond a w h f).faceBase false,
      (rectanglePrimalEdgeBond a w h f).faceBase true)) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v := by
  let e := DualityExt.rectangleDualEdgeEquiv a w h f
  have he : e.val=s(u,v) := by
    apply Sym2.map.injective Subtype.val_injective
    exact (rectangle_dual_edge_face_pair a w h f).trans hpair.symm
  have heA : e ∈ auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A := by
    apply (mem_auxiliaryClosedConfiguration _ A e).mpr
    simpa only [e,Equiv.symm_apply_apply] using hf
  rw [auxiliaryClosedConfiguration_rectangle_eq] at heA
  exact (openGraph_adj _ _ u v).mpr ⟨e,heA,he⟩

/-- True-dual steps change height by at most one. Any step that changes
height lies in an INTERIOR face column; side ports cannot be traversed
vertically. This excludes spurious expanded-boundary steps in band clipping. -/
theorem rectangle_dual_step_height_and_column (a : LatticeVertex) (w h : ℕ)
    {u v : RectangleDualVertex a w h} (huv : (rectangleDualGraph a w h).Adj u v) :
    |u.val.2-v.val.2| ≤ 1 ∧
      (u.val.2 ≠ v.val.2 → a.1 ≤ u.val.1 ∧ u.val.1 < a.1+(w : ℤ)) := by
  obtain ⟨f,hpair⟩ := rectangle_dual_step_original_bond a w h huv
  have hends := rectanglePrimalEdgeBond_endpoints_mem_public a w h f
  generalize hb : rectanglePrimalEdgeBond a w h f = b at hpair hends
  rcases b with ⟨⟨x,y⟩,axis⟩
  rcases u with ⟨⟨ux,uy⟩,hu⟩
  rcases v with ⟨⟨vx,vy⟩,hv⟩
  simp only [mem_latticeRectangle] at hends
  cases axis <;>
    simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target,
      Sym2.eq_iff,Prod.mk.injEq] at hpair hends <;>
    simp only [abs_eq_max_neg] <;> omega

end
end PottsContinuity.Push
