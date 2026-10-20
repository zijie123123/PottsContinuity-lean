-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleOpenWalkInterpolation.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleOpenExtension
public import PottsContinuity.FKC.FiniteFK.RectangleCrossingIntersection
public import PottsContinuity.FKC.Curves.DualWalkAvoidance
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Curves PottsContinuity.FKC.Medial
open Set
open unitInterval
noncomputable section

def rectangleInterpolationUnitMesh : PositiveMesh := ⟨1, by norm_num⟩

def rectangleOpenOutsideWalkToLatticeWalk {a : LatticeVertex} {w h : ℕ}
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) : squareLattice.Walk u.val v.val :=
  openPrimalWalkToLatticeWalk
    (p.map (rectangleOpenOutsidePrimalGraphHom a w h A))

theorem rectangleOpenOutsideWalkToLatticeWalk_eq_squareMap
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) :
    rectangleOpenOutsideWalkToLatticeWalk A p =
      p.map (rectangleOpenGraphToSquare a w h A) := by
  induction p with
  | nil => rfl
  | @cons u v z huv p ih =>
      dsimp [rectangleOpenOutsideWalkToLatticeWalk, openPrimalWalkToLatticeWalk,
        rectangleOpenOutsidePrimalGraphHom, rectangleOpenGraphToSquare]
      congr 1

theorem rectangleOpenOutsideWalkPath_coordinate_bounds
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) (t : I) :
    (a.1 : ℝ) ≤ (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).re ∧
    (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).re ≤ ((a.1 + w : ℤ) : ℝ) ∧
    (a.2 : ℝ) ≤ (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).im ∧
    (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).im ≤ ((a.2 + h : ℤ) : ℝ) := by
  rw [rectangleOpenOutsideWalkToLatticeWalk_eq_squareMap]
  apply latticeWalkPath_coordinate_bounds
  intro x hx
  have hxrect := rectangleOpenWalk_support_mapped_mem a w h A p hx
  have hxbox := (mem_latticeRectangle a x w h).mp hxrect
  exact ⟨by exact_mod_cast hxbox.1.1, by exact_mod_cast hxbox.1.2,
    by exact_mod_cast hxbox.2.1, by exact_mod_cast hxbox.2.2⟩

theorem rectangleOpenOutsideWalkPath_source
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) :
    latticeWalkPath rectangleInterpolationUnitMesh (rectangleOpenOutsideWalkToLatticeWalk A p) 0 =
      latticeEmbed rectangleInterpolationUnitMesh u.val := by
  simp [rectangleOpenOutsideWalkToLatticeWalk]

theorem rectangleOpenOutsideWalkPath_target
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) :
    latticeWalkPath rectangleInterpolationUnitMesh (rectangleOpenOutsideWalkToLatticeWalk A p) 1 =
      latticeEmbed rectangleInterpolationUnitMesh v.val := by
  simp [rectangleOpenOutsideWalkToLatticeWalk]

theorem centeredRectangleOpenOutsideWalkPath_coordinate_bounds
    (n : ℕ) (A : Configuration (rectangleGraph (-(n : ℤ), 0) (2 * n) n))
    {u v : RectangleVertex (-(n : ℤ), 0) (2 * n) n}
    (p : (openGraph (rectangleGraph (-(n : ℤ), 0) (2 * n) n) A).Walk u v)
    (t : I) :
    -(n : ℝ) ≤ (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).re ∧
    (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).re ≤ (n : ℝ) ∧
    0 ≤ (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).im ∧
    (latticeWalkPath rectangleInterpolationUnitMesh
      (rectangleOpenOutsideWalkToLatticeWalk A p) t).im ≤ (n : ℝ) := by
  have hb := rectangleOpenOutsideWalkPath_coordinate_bounds
    (-(n : ℤ), 0) (2 * n) n A p t
  constructor
  · simpa using hb.1
  constructor
  · have hh := hb.2.1
    push_cast at hh
    norm_num at hh
    nlinarith [hh]
  constructor
  · simpa using hb.2.2.1
  · simpa using hb.2.2.2

end
end PottsContinuity.FKC.FiniteFK
