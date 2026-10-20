/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleTranslation.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

noncomputable section

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism transports literal wired boundary conditions to the
wired condition on the image set. -/
theorem boundaryConditionIso_wired_image (e : G ≃g H) (B : Set V) :
    boundaryConditionIso e (BoundaryCondition.wired B) =
      BoundaryCondition.wired (e '' B) := by
  simp only [boundaryConditionIso, BoundaryCondition.wired]
  rw [BoundaryCondition.mk.injEq]
  constructor
  · rfl
  · apply Setoid.ext
    intro x y
    change (e.symm x = e.symm y ∨ e.symm x ∈ B ∧ e.symm y ∈ B) ↔
      (x = y ∨ x ∈ e '' B ∧ y ∈ e '' B)
    have hmem (z : W) : z ∈ e '' B ↔ e.symm z ∈ B := by
      constructor
      · rintro ⟨v, hv, rfl⟩
        simpa using hv
      · intro hz
        exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
    constructor
    · rintro (h | h)
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr ⟨(hmem x).2 h.1, (hmem y).2 h.2⟩
    · rintro (h | h)
      · exact Or.inl (congrArg e.symm h)
      · exact Or.inr ⟨(hmem x).1 h.1, (hmem y).1 h.2⟩

 theorem latticeRectangle_translate_mem (t a v : LatticeVertex)
    (w h : ℕ) (hv : v ∈ latticeRectangle a w h) :
    latticeTranslate t v ∈ latticeRectangle (latticeTranslate t a) w h := by
  simp only [mem_latticeRectangle] at hv ⊢
  rcases a with ⟨ax, ay⟩
  rcases t with ⟨tx, ty⟩
  rcases v with ⟨x, y⟩
  dsimp [latticeTranslate] at *
  rcases hv with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

 theorem latticeRectangle_translate_back_mem (t a v : LatticeVertex)
    (w h : ℕ) (hv : v ∈ latticeRectangle (latticeTranslate t a) w h) :
    latticeTranslate (-t) v ∈ latticeRectangle a w h := by
  simp only [mem_latticeRectangle] at hv ⊢
  rcases a with ⟨ax, ay⟩
  rcases t with ⟨tx, ty⟩
  rcases v with ⟨x, y⟩
  dsimp [latticeTranslate] at *
  rcases hv with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- A coordinate translation as an equivalence of the actual closed rectangle
vertex carriers. -/
def rectangleVertexTranslationEquiv (t a : LatticeVertex) (w h : ℕ) :
    RectangleVertex a w h ≃ RectangleVertex (latticeTranslate t a) w h where
  toFun v := ⟨latticeTranslate t v.val,
    latticeRectangle_translate_mem t a v.val w h v.property⟩
  invFun v := ⟨latticeTranslate (-t) v.val,
    latticeRectangle_translate_back_mem t a v.val w h v.property⟩
  left_inv v := by
    apply Subtype.ext
    exact latticeTranslate_neg_cancel t v.val
  right_inv v := by
    apply Subtype.ext
    ext <;> dsimp [latticeTranslate] <;> omega

@[simp] theorem rectangleVertexTranslationEquiv_val (t a : LatticeVertex)
    (w h : ℕ) (v : RectangleVertex a w h) :
    (rectangleVertexTranslationEquiv t a w h v).val = latticeTranslate t v.val := rfl

/-- Translation is a graph isomorphism between equal-size lattice rectangles. -/
def rectangleGraphTranslationIso (t a : LatticeVertex) (w h : ℕ) :
    rectangleGraph a w h ≃g rectangleGraph (latticeTranslate t a) w h where
  toEquiv := rectangleVertexTranslationEquiv t a w h
  map_rel_iff' := by
    intro u v
    simpa only [rectangleGraph_adj_iff, rectangleVertexTranslationEquiv_val] using
      (squareLattice_adj_translate_iff t u.val v.val)

@[simp] theorem rectangleGraphTranslationIso_val (t a : LatticeVertex)
    (w h : ℕ) (v : RectangleVertex a w h) :
    (rectangleGraphTranslationIso t a w h v).val = latticeTranslate t v.val := rfl

end
end PottsContinuity.PlanarMixed.Square
