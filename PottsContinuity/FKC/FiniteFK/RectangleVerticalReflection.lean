-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleVerticalReflection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Rectangle
public import PottsContinuity.FKC.FiniteFK.RectangleTranslation
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomCollar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

 theorem rectangleVerticalReflection_mem (a : LatticeVertex) (w h : ℕ)
    (v : RectangleVertex a w h) :
    (v.val.1, 2 * a.2 + (h : ℤ) - v.val.2) ∈ latticeRectangle a w h := by
  rcases v with ⟨⟨x, y⟩, hv⟩
  have hb := (mem_latticeRectangle a (x, y) w h).mp hv
  change (x, 2 * a.2 + (h : ℤ) - y) ∈ latticeRectangle a w h
  exact (mem_latticeRectangle a (x, 2 * a.2 + (h : ℤ) - y) w h).mpr
    ⟨hb.1, ⟨by omega, by omega⟩⟩

/-- Reflection in the horizontal midline of an actual closed rectangle. -/
def rectangleVerticalReflectionVertexEquiv (a : LatticeVertex) (w h : ℕ) :
    RectangleVertex a w h ≃ RectangleVertex a w h where
  toFun v := ⟨(v.val.1, 2 * a.2 + (h : ℤ) - v.val.2),
    rectangleVerticalReflection_mem a w h v⟩
  invFun v := ⟨(v.val.1, 2 * a.2 + (h : ℤ) - v.val.2),
    rectangleVerticalReflection_mem a w h v⟩
  left_inv v := by
    apply Subtype.ext
    ext <;> simp
  right_inv v := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem rectangleVerticalReflectionVertexEquiv_val
    (a : LatticeVertex) (w h : ℕ) (v : RectangleVertex a w h) :
    (rectangleVerticalReflectionVertexEquiv a w h v).val =
      (v.val.1, 2 * a.2 + (h : ℤ) - v.val.2) := rfl

def rectangleGraphVerticalReflectionIso (a : LatticeVertex) (w h : ℕ) :
    rectangleGraph a w h ≃g rectangleGraph a w h where
  toEquiv := rectangleVerticalReflectionVertexEquiv a w h
  map_rel_iff' := by
    intro u v
    rw [rectangleGraph_adj_iff, rectangleGraph_adj_iff,
      rectangleVerticalReflectionVertexEquiv_val, rectangleVerticalReflectionVertexEquiv_val,
      squareLattice_adj_iff, squareLattice_adj_iff]
    dsimp
    omega

/-- The actual top row of the closed rectangle, viewed as a vertex subset. -/
def rectangleVerticalReflectionTopSet (a : LatticeVertex) (w h : ℕ) :
    Set (RectangleVertex a w h) :=
  {v | v.val.2 = a.2 + (h : ℤ)}

theorem rectangleVerticalReflection_image_bottom_eq_top
    (a : LatticeVertex) (w h : ℕ) :
    rectangleGraphVerticalReflectionIso a w h ''
      rectangleArbitraryBottomCollarBottom a w h =
        rectangleVerticalReflectionTopSet a w h := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change 2 * a.2 + (h : ℤ) - u.val.2 = a.2 + (h : ℤ)
    change u.val.2 = a.2 at hu
    rw [hu]
    ring
  · intro hv
    change v.val.2 = a.2 + (h : ℤ) at hv
    refine ⟨rectangleGraphVerticalReflectionIso a w h v, ?_, ?_⟩
    · change 2 * a.2 + (h : ℤ) - v.val.2 = a.2
      rw [hv]
      ring
    · apply Subtype.ext
      change (rectangleVerticalReflectionVertexEquiv a w h
        (rectangleVerticalReflectionVertexEquiv a w h v)).val = v.val
      rw [rectangleVerticalReflectionVertexEquiv_val,
        rectangleVerticalReflectionVertexEquiv_val]
      ring_nf

theorem law_rectangleVerticalReflection_bottom_map
    (q : ClusterWeight) (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) q
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))).map
        (configurationIso (rectangleGraphVerticalReflectionIso a w h)) =
      law (rectangleGraph a w h) q
        (BoundaryCondition.wired (rectangleVerticalReflectionTopSet a w h)) := by
  rw [law_configurationIso_map, boundaryConditionIso_wired_image,
    rectangleVerticalReflection_image_bottom_eq_top]

end
end PottsContinuity.FKC.FiniteFK
