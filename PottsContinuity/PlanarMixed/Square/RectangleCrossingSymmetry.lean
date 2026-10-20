/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleCrossingSymmetry.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.RectangleEvents
public import PottsContinuity.PD.FK.WiredBoxTranslation
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK MeasureTheory

noncomputable section

def latticeCoordinateSwap (v : LatticeVertex) : LatticeVertex := (v.2, v.1)

@[simp] theorem latticeCoordinateSwap_swap (v : LatticeVertex) :
    latticeCoordinateSwap (latticeCoordinateSwap v) = v := by
  ext <;> rfl

lemma squareLattice_adj_coordinateSwap_iff (u v : LatticeVertex) :
    squareLattice.Adj (latticeCoordinateSwap u) (latticeCoordinateSwap v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeCoordinateSwap]
  tauto

def rectangleVertexCoordinateSwapEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleVertex a w h ≃ RectangleVertex (latticeCoordinateSwap a) h w where
  toFun v := ⟨latticeCoordinateSwap v.val, by
    have hv := (mem_latticeRectangle a v.val w h).mp v.property
    rw [mem_latticeRectangle, latticeCoordinateSwap]
    exact ⟨⟨hv.2.1, by simpa [latticeCoordinateSwap] using hv.2.2⟩,
      ⟨hv.1.1, by simpa [latticeCoordinateSwap] using hv.1.2⟩⟩⟩
  invFun v := ⟨latticeCoordinateSwap v.val, by
    have hv := (mem_latticeRectangle (latticeCoordinateSwap a) v.val h w).mp v.property
    rw [mem_latticeRectangle, latticeCoordinateSwap]
    exact ⟨⟨hv.2.1, by simpa [latticeCoordinateSwap] using hv.2.2⟩,
      ⟨hv.1.1, by simpa [latticeCoordinateSwap] using hv.1.2⟩⟩⟩
  left_inv v := by apply Subtype.ext; exact latticeCoordinateSwap_swap v.val
  right_inv v := by apply Subtype.ext; exact latticeCoordinateSwap_swap v.val

def rectangleGraphCoordinateSwapIso (a : LatticeVertex) (w h : ℕ) :
    rectangleGraph a w h ≃g rectangleGraph (latticeCoordinateSwap a) h w where
  toEquiv := rectangleVertexCoordinateSwapEquiv a w h
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_coordinateSwap_iff u.val v.val

@[simp] theorem rectangleVertexCoordinateSwapEquiv_val (a : LatticeVertex) (w h : ℕ)
    (v : RectangleVertex a w h) :
    (rectangleVertexCoordinateSwapEquiv a w h v).val = latticeCoordinateSwap v.val := rfl

lemma coordinateSwap_leftSide_iff_bottom (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    v ∈ rectangleLeftSide a w h ↔
      latticeCoordinateSwap v ∈ rectangleBottomSide (latticeCoordinateSwap a) h w := by
  rw [rectangleLeftSide, rectangleBottomSide]
  simp only [Finset.mem_filter, mem_latticeRectangle]
  constructor
  · rintro ⟨⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩, hx⟩
    constructor
    · change ((a.2 ≤ v.2 ∧ v.2 ≤ a.2 + (h : ℤ)) ∧
        (a.1 ≤ v.1 ∧ v.1 ≤ a.1 + (w : ℤ)))
      exact ⟨⟨hylo, hyhi⟩, ⟨hxlo, hxhi⟩⟩
    · exact hx
  · rintro ⟨⟨⟨hylo, hyhi⟩, ⟨hxlo, hxhi⟩⟩, hy⟩
    constructor
    · exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
    · exact hy

lemma coordinateSwap_rightSide_iff_top (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    v ∈ rectangleRightSide a w h ↔
      latticeCoordinateSwap v ∈ rectangleTopSide (latticeCoordinateSwap a) h w := by
  rw [rectangleRightSide, rectangleTopSide]
  simp only [Finset.mem_filter, mem_latticeRectangle]
  constructor
  · rintro ⟨⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩, hx⟩
    constructor
    · change ((a.2 ≤ v.2 ∧ v.2 ≤ a.2 + (h : ℤ)) ∧
        (a.1 ≤ v.1 ∧ v.1 ≤ a.1 + (w : ℤ)))
      exact ⟨⟨hylo, hyhi⟩, ⟨hxlo, hxhi⟩⟩
    · exact hx
  · rintro ⟨⟨⟨hylo, hyhi⟩, ⟨hxlo, hxhi⟩⟩, hy⟩
    constructor
    · exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
    · exact hy

theorem rectangleHorizontalCrossingEvent_coordinateSwap_iff
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    A ∈ rectangleHorizontalCrossingEvent a w h ↔
      configurationIso (rectangleGraphCoordinateSwapIso a w h) A ∈
        rectangleVerticalCrossingEvent (latticeCoordinateSwap a) h w := by
  constructor
  · rintro ⟨u, v, hu, hv, hconn⟩
    refine ⟨rectangleVertexCoordinateSwapEquiv a w h u,
      rectangleVertexCoordinateSwapEquiv a w h v, ?_, ?_, ?_⟩
    · exact (coordinateSwap_leftSide_iff_bottom a w h u.val).mp hu
    · exact (coordinateSwap_rightSide_iff_top a w h v.val).mp hv
    · exact (actualConnected_configurationIso (rectangleGraphCoordinateSwapIso a w h)
        A u v).mpr hconn
  · rintro ⟨u, v, hu, hv, hconn⟩
    let e := rectangleVertexCoordinateSwapEquiv a w h
    refine ⟨e.symm u, e.symm v, ?_, ?_, ?_⟩
    · have hswap : latticeCoordinateSwap (e.symm u).val = u.val := by
        exact congrArg Subtype.val (e.apply_symm_apply u)
      have hs := (coordinateSwap_leftSide_iff_bottom a w h (e.symm u).val).mpr
        (by simpa [hswap] using hu)
      exact hs
    · have hswap : latticeCoordinateSwap (e.symm v).val = v.val := by
        exact congrArg Subtype.val (e.apply_symm_apply v)
      have hs := (coordinateSwap_rightSide_iff_top a w h (e.symm v).val).mpr
        (by simpa [hswap] using hv)
      exact hs
    · have hu' : e (e.symm u) = u := e.apply_symm_apply u
      have hv' : e (e.symm v) = v := e.apply_symm_apply v
      simpa [hu', hv'] using
        (actualConnected_configurationIso (rectangleGraphCoordinateSwapIso a w h)
          A (e.symm u) (e.symm v)).mp hconn

attribute [local instance] configurationMeasurableSpace

end
end PottsContinuity.PlanarMixed.Square
