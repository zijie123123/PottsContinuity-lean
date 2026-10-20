-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCollarBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCollarConfiguration

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The three sides of the inner expanded face-base rectangle that remain on
the boundary of the larger dual rectangle after adding a bottom collar. -/
def generalRectangleDualBottomCollarInnerThreeSides
    (a : LatticeVertex) (w h : ℕ) : Set (generalRectangleDualBottomCollarInnerVertex a w h) :=
  {v | v.val.1 = a.1 - 1 ∨ v.val.1 = a.1 + (w : ℤ) ∨ v.val.2 = a.2 + (h : ℤ)}

/-- The restriction of the outer dual boundary to the embedded inner face bases
is exactly the inner left, right, and top sides. -/
theorem generalRectangleDualBottomCollar_boundary_mem
    (a : LatticeVertex) (w h : ℕ)
    (v : generalRectangleDualBottomCollarInnerVertex a w h) :
    v.val ∈ rectangleDualBoundary (a.1, a.2 - 1) w (h + 1) ↔
      v ∈ generalRectangleDualBottomCollarInnerThreeSides a w h := by
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
    have hnot : v.val ∉ rectangleDualInterior (a.1, a.2 - 1) w (h + 1) := hmem.2
    simp only [generalRectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq]
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hnot
    omega
  · intro hv
    have hvouter : v.val ∈ rectangleDualExpanded (a.1, a.2 - 1) w (h + 1) :=
      generalRectangleDualBottomCollar_vertex_subset a w h v.property
    refine Finset.mem_filter.mpr ⟨hvouter, ?_⟩
    intro hi
    simp only [rectangleDualInterior, Finset.mem_filter, rectangleDualExpanded,
      mem_latticeRectangle] at hi
    simp only [generalRectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hv
    omega

@[simp] theorem generalRectangleDualBottomCollar_outerBoundaryCondition_pullback
    (a : LatticeVertex) (w h : ℕ)
    (u v : generalRectangleDualBottomCollarInnerVertex a w h) :
    (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 1)).partition.r
      (generalRectangleDualBottomCollar_vertexEmbedding a w h u)
      (generalRectangleDualBottomCollar_vertexEmbedding a w h v) ↔
      u = v ∨ u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h ∧
        v ∈ generalRectangleDualBottomCollarInnerThreeSides a w h := by
  rw [rectangleDualBoundaryCondition_rel]
  constructor
  · rintro (hEq | ⟨hu, hv⟩)
    · left
      apply (generalRectangleDualBottomCollar_vertexEmbedding a w h).injective
      exact hEq
    · exact Or.inr ⟨(generalRectangleDualBottomCollar_boundary_mem a w h u).mp hu,
        (generalRectangleDualBottomCollar_boundary_mem a w h v).mp hv⟩
  · rintro (hEq | ⟨hu, hv⟩)
    · left
      exact congrArg (generalRectangleDualBottomCollar_vertexEmbedding a w h) hEq
    · exact Or.inr ⟨(generalRectangleDualBottomCollar_boundary_mem a w h u).mpr hu,
        (generalRectangleDualBottomCollar_boundary_mem a w h v).mpr hv⟩

end
end PottsContinuity.FKC.FiniteFK
