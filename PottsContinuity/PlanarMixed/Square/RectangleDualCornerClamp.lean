/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualCornerClamp.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerCore
public import PottsContinuity.PlanarMixed.Square.GeneralRectangleDualBottomLeaves
public import PottsContinuity.PD.Duality.RectangleFlowDimension
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial
noncomputable section

def rectangleDualCornerClamp (a : LatticeVertex) (w h : ℕ)
    (v : RectangleDualVertex a w h) : RectangleVertex a w h := by
  let z : LatticeVertex := (max v.1.1 a.1, max v.1.2 a.2)
  have hz : z ∈ latticeRectangle a w h := by
    have hv := v.2
    change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hv
    rw [mem_latticeRectangle] at hv
    rcases hv with ⟨hx, hy⟩
    change z ∈ latticeRectangle a w h
    rw [mem_latticeRectangle]
    constructor
    · constructor
      · exact le_max_right _ _
      · exact max_le_iff.mpr ⟨by omega, by omega⟩
    · constructor
      · exact le_max_right _ _
      · exact max_le_iff.mpr ⟨by omega, by omega⟩
  exact ⟨z, hz⟩

@[simp] theorem rectangleDualCornerClamp_val (a : LatticeVertex) (w h : ℕ)
    (v : RectangleDualVertex a w h) :
    (rectangleDualCornerClamp a w h v).1 =
      (max v.1.1 a.1, max v.1.2 a.2) := rfl

theorem rectangleDualCornerClamp_section (a : LatticeVertex) (w h : ℕ)
    (v : RectangleVertex a w h) :
    rectangleDualCornerClamp a w h
      (rectangleDualCornerCoreEmbedding a w h v) = v := by
  apply Subtype.ext
  change (max v.1.1 a.1, max v.1.2 a.2) = v.1
  have hv := v.2
  rw [mem_latticeRectangle] at hv
  rcases hv with ⟨hx, hy⟩
  simp [max_eq_left hx.1, max_eq_left hy.1]

theorem rectangleDualCornerClamp_embedding_of_mem_corner (a : LatticeVertex)
    (w h : ℕ) (v : RectangleDualVertex a w h)
    (hx : a.1 ≤ v.1.1) (hy : a.2 ≤ v.1.2) :
    rectangleDualCornerCoreEmbedding a w h (rectangleDualCornerClamp a w h v) = v := by
  apply Subtype.ext
  change (max v.1.1 a.1, max v.1.2 a.2) = v.1
  simp [max_eq_left hx, max_eq_left hy]

private theorem corner_adj_primal_bond
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualGraph a w h).Adj u v) :
    ∃ b : RectanglePrimalBond a w h,
      s(u.1, v.1) = s(b.1.faceBase false, b.1.faceBase true) := by
  obtain ⟨e, he⟩ := (rectangleDualGraph_adj_iff a w h u v).mp hadj
  let b : RectanglePrimalBond a w h := (rectanglePrimalEdgeBondEquiv a w h) e.primalEdge
  refine ⟨b, ?_⟩
  have hpair : s(u.1, v.1) = s(e.crossingBond.source, e.crossingBond.target) := by
    simpa [rectangleDualCarrierPair, rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val] using congrArg (Sym2.map Subtype.val) he
  have hcross : e.crossingBond = dualBondOfPrimal b.1 := by
    exact e.crossingBond_eq
  rw [hcross, dualBondOfPrimal_source, dualBondOfPrimal_target] at hpair
  exact hpair

private theorem rectangleDualCornerLeftRow_adj_neighbor
    (a : LatticeVertex) (w h : ℕ) (y : ℤ)
    (u v : RectangleDualVertex a w h)
    (hu : u.1 = (a.1 - 1, y))
    (hadj : (rectangleDualGraph a w h).Adj u v) :
    v.1 = (a.1, y) := by
  obtain ⟨b, hpair⟩ := corner_adj_primal_bond a w h u v hadj
  rcases b with ⟨bond, hbs, hbt⟩
  rcases bond with ⟨⟨bx, byy⟩, axis⟩
  cases axis <;>
    rcases Sym2.eq_iff.mp hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    simp [LatticeBond.faceBase, hu, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle] at h₁ h₂ hbs hbt <;>
    (rcases h₁ with ⟨hbx, hby⟩; subst bx; simp_all [Prod.ext_iff])

private theorem rectangleDualCornerClamp_eq_of_left_outside
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualGraph a w h).Adj u v)
    (hout : ¬ (a.1 ≤ u.1.1 ∧ a.2 ≤ u.1.2)) :
    rectangleDualCornerClamp a w h u = rectangleDualCornerClamp a w h v := by
  have huBox := u.2
  change u.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at huBox
  rw [mem_latticeRectangle] at huBox
  rcases huBox with ⟨hx, hy⟩
  by_cases hbottom : u.1.2 < a.2
  · have hu : u.1 = (u.1.1, a.2 - 1) := by
      apply Prod.ext
      · rfl
      · omega
    obtain ⟨hcoord, hxlo, hxhi⟩ :=
      generalRectangleDualBottomRow_adj_neighbor a w h u.1.1 u v hu hadj
    apply Subtype.ext
    change (max u.1.1 a.1, max u.1.2 a.2) =
      (max v.1.1 a.1, max v.1.2 a.2)
    rw [hu, hcoord]
    simp [max_eq_left hxlo]
  · have hleft : u.1.1 < a.1 := by
      by_contra hn
      exact hout ⟨by omega, by omega⟩
    have hu : u.1 = (a.1 - 1, u.1.2) := by
      apply Prod.ext
      · omega
      · rfl
    have hcoord := rectangleDualCornerLeftRow_adj_neighbor a w h u.1.2 u v hu hadj
    apply Subtype.ext
    change (max u.1.1 a.1, max u.1.2 a.2) =
      (max v.1.1 a.1, max v.1.2 a.2)
    rw [hu, hcoord]
    simp

theorem rectangleDualCornerClamp_eq_of_adj_endpoint_outside
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualGraph a w h).Adj u v)
    (hout : ¬ (a.1 ≤ u.1.1 ∧ a.2 ≤ u.1.2) ∨
      ¬ (a.1 ≤ v.1.1 ∧ a.2 ≤ v.1.2)) :
    rectangleDualCornerClamp a w h u = rectangleDualCornerClamp a w h v := by
  rcases hout with hu | hv
  · exact rectangleDualCornerClamp_eq_of_left_outside a w h u v hadj hu
  · exact (rectangleDualCornerClamp_eq_of_left_outside a w h v u hadj.symm hv).symm

end
end PottsContinuity.PlanarMixed.Square
