/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualTopLeaves.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.GeneralRectangleDualBottomLeaves
public import PottsContinuity.PlanarMixed.Square.RectangleDualVerticalReflection
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

private theorem rectangleDualTopRow_reflect_bottom
    (a : LatticeVertex) (w h : ℕ) (x : ℤ)
    (u : RectangleDualVertex a w h)
    (hu : u.1 = (x, a.2 + (h : ℤ))) :
    (rectangleDualVerticalReflectionVertexEquiv a w h u).1 =
      (x, a.2 - 1) := by
  rw [rectangleDualVerticalReflectionVertexEquiv_val, hu]
  congr 1
  omega

/-- Every actual neighbor of a top-row face base is its unique vertical
parent. The lateral coordinate must lie in the primal-width interval; the
two corners therefore have no actual neighbors. -/
theorem rectangleDualTopRow_adj_neighbor
    (a : LatticeVertex) (w h : ℕ) (x : ℤ)
    (u v : RectangleDualVertex a w h)
    (hu : u.1 = (x, a.2 + (h : ℤ)))
    (hadj : (rectangleDualGraph a w h).Adj u v) :
    v.1 = (x, a.2 + (h : ℤ) - 1) ∧
      a.1 ≤ x ∧ x < a.1 + (w : ℤ) := by
  let ρ := rectangleDualVerticalReflectionVertexEquiv a w h
  let ρG := rectangleDualGraphVerticalReflectionIso a w h
  have hu' : (ρ u).1 = (x, a.2 - 1) := by
    exact rectangleDualTopRow_reflect_bottom a w h x u hu
  have hadj' : (rectangleDualGraph a w h).Adj (ρ u) (ρ v) :=
    (ρG.map_rel_iff).2 hadj
  obtain ⟨hv', hx₁, hx₂⟩ :=
    generalRectangleDualBottomRow_adj_neighbor a w h x (ρ u) (ρ v) hu' hadj'
  have hback : ρ (ρ v) = v := ρ.left_inv v
  have hpair := congrArg Subtype.val hback
  change (ρ (ρ v)).1 = v.1 at hpair
  rw [rectangleDualVerticalReflectionVertexEquiv_val, hv'] at hpair
  have hvTop : v.1 = (x, a.2 + (h : ℤ) - 1) := by
    apply hpair.symm.trans
    congr 1
    omega
  exact ⟨hvTop, hx₁, hx₂⟩

end
end PottsContinuity.PlanarMixed.Square
