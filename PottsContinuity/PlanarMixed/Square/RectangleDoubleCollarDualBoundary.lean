/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarDualBoundary.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.RectangleDualCarrier
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

noncomputable section

abbrev rectangleDoubleCollarDualInnerVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleDualVertex a w h

abbrev rectangleDoubleCollarDualOuterVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleDualVertex (a.1, a.2 - 1) w (h + 2)

/-- The two vertical sides of the inner expanded dual rectangle, viewed as one
set. The outer boundary wires their union as a single block. -/
def rectangleDoubleCollarDualInnerVerticalSides
    (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleDoubleCollarDualInnerVertex a w h) :=
  {v | v.val.1 = a.1 - 1 ∨ v.val.1 = a.1 + (w : ℤ)}

theorem rectangleDoubleCollarDual_vertex_subset (a : LatticeVertex) (w h : ℕ) :
    rectangleDualExpanded a w h ⊆
      rectangleDualExpanded (a.1, a.2 - 1) w (h + 2) := by
  intro z hz
  rw [rectangleDualExpanded, mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  exact ⟨⟨hx₁, hx₂⟩, ⟨by omega, by omega⟩⟩

/-- Literal same-coordinate inclusion of inner expanded face bases into the
outer dual rectangle with one added row on each side. -/
def rectangleDoubleCollarDual_vertexEmbedding (a : LatticeVertex) (w h : ℕ) :
    rectangleDoubleCollarDualInnerVertex a w h ↪
      rectangleDoubleCollarDualOuterVertex a w h :=
  ⟨fun v => ⟨v.val, rectangleDoubleCollarDual_vertex_subset a w h v.property⟩,
    fun x y hxy => by
      have hv : x.val = y.val :=
        congrArg (fun z : rectangleDoubleCollarDualOuterVertex a w h => z.val) hxy
      exact Subtype.ext hv⟩

@[simp] theorem rectangleDoubleCollarDual_vertexEmbedding_val
    (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarDualInnerVertex a w h) :
    (rectangleDoubleCollarDual_vertexEmbedding a w h v).val = v.val := rfl

/-- Among inner expanded face bases, membership in the outer expanded
rectangle's boundary is exactly membership in either vertical side. -/
theorem rectangleDoubleCollarDual_boundary_mem
    (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarDualInnerVertex a w h) :
    v.val ∈ rectangleDualBoundary (a.1, a.2 - 1) w (h + 2) ↔
      v ∈ rectangleDoubleCollarDualInnerVerticalSides a w h := by
  have hprop := v.property
  change v.val ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hprop
  rw [mem_latticeRectangle] at hprop
  have hvcoord : a.1 - 1 ≤ v.val.1 ∧ v.val.1 ≤ a.1 + (w : ℤ) ∧
      a.2 - 1 ≤ v.val.2 ∧ v.val.2 ≤ a.2 + (h : ℤ) := by
    rcases hprop with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    exact ⟨hx₁, by omega, by omega, by omega⟩
  constructor
  · intro hb
    have hmem := Finset.mem_filter.mp hb
    have hnot : v.val ∉ rectangleDualInterior (a.1, a.2 - 1) w (h + 2) := hmem.2
    simp only [rectangleDoubleCollarDualInnerVerticalSides, Set.mem_ofPred_eq]
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hnot
    omega
  · intro hv
    have hvouter : v.val ∈ rectangleDualExpanded (a.1, a.2 - 1) w (h + 2) :=
      rectangleDoubleCollarDual_vertex_subset a w h v.property
    refine Finset.mem_filter.mpr ⟨hvouter, ?_⟩
    intro hi
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hi
    simp only [rectangleDoubleCollarDualInnerVerticalSides, Set.mem_ofPred_eq] at hv
    omega

/-- The outer wired boundary pulls back to the two vertical sides wired
together as one block; corners and degenerate dimensions follow the literal
expanded-rectangle boundary definition. -/
@[simp] theorem rectangleDoubleCollarDual_outerBoundaryCondition_pullback
    (a : LatticeVertex) (w h : ℕ)
    (u v : rectangleDoubleCollarDualInnerVertex a w h) :
    (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 2)).partition.r
      (rectangleDoubleCollarDual_vertexEmbedding a w h u)
      (rectangleDoubleCollarDual_vertexEmbedding a w h v) ↔
      u = v ∨ u ∈ rectangleDoubleCollarDualInnerVerticalSides a w h ∧
        v ∈ rectangleDoubleCollarDualInnerVerticalSides a w h := by
  rw [rectangleDualBoundaryCondition_rel]
  constructor
  · rintro (hEq | ⟨hu, hv⟩)
    · left
      apply (rectangleDoubleCollarDual_vertexEmbedding a w h).injective
      exact hEq
    · exact Or.inr ⟨(rectangleDoubleCollarDual_boundary_mem a w h u).mp hu,
        (rectangleDoubleCollarDual_boundary_mem a w h v).mp hv⟩
  · rintro (hEq | ⟨hu, hv⟩)
    · left
      exact congrArg (rectangleDoubleCollarDual_vertexEmbedding a w h) hEq
    · exact Or.inr ⟨(rectangleDoubleCollarDual_boundary_mem a w h u).mpr hu,
        (rectangleDoubleCollarDual_boundary_mem a w h v).mpr hv⟩

end
end PottsContinuity.PlanarMixed.Square
