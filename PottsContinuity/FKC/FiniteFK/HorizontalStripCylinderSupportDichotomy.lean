-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCylinderSupportDichotomy.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopCylinders
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopExhaustion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutCylinderSupport
public import Mathlib.Tactic

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open Finset

noncomputable section

local instance cylinderDichotomyEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance cylinderDichotomyEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

/-- Either a finite edge cylinder is supported by some horizontal strip
rectangle, or it is empty in every finite strip rectangle. -/
theorem horizontalStripRectangleCylinder_finiteSupport_or_empty
    (n : ℕ) (F : Finset squareLattice.edgeSet) :
    (∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) ∨
    ∀ N : ℕ, horizontalStripRectangleCylinderEvent N n F = ∅ := by
  classical
  by_cases hsupp : ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)
  · exact Or.inl hsupp
  · right
    intro N
    ext A
    constructor
    · intro hA
      change F ⊆ A.image (horizontalStripRectangleOriginalEdge N n) at hA
      apply False.elim
      apply hsupp
      refine ⟨N, ?_⟩
      intro e he
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (hA he)
      exact Set.mem_range.mpr ⟨x, hxe⟩
    · simp

theorem horizontalStripRectangleCylinder_probability_zero_of_no_finiteSupport
    (q : ClusterWeight) (n N : ℕ) (F : Finset squareLattice.edgeSet)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hNo : ¬ ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    measure (horizontalStripCutRectangle N n) q ξ
      (horizontalStripRectangleCylinderEvent N n F) = 0 := by
  have hempty := (horizontalStripRectangleCylinder_finiteSupport_or_empty n F).resolve_left hNo N
  rw [hempty]
  exact measure_empty

theorem horizontalStripTopWiredLimit_allOpen_eq_zero_of_no_finiteSupport
    (q : ClusterWeight) (n : ℕ) (F : Finset squareLattice.edgeSet)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ))
    (hNo : ¬ ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    μ (LatticeConfiguration.allOpen F) = 0 := by
  have hempty := (horizontalStripRectangleCylinder_finiteSupport_or_empty n F).resolve_left hNo
  have hzero : ∀ N : ℕ,
      horizontalStripTopWiredProbabilityMeasures q n N
        (LatticeConfiguration.allOpen F) = 0 := by
    intro N
    change ((horizontalStripRectangleProbabilityMeasure q N n
      (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F)).toNNReal = 0
    rw [horizontalStripRectangleProbabilityMeasure_allOpen q N n
      (horizontalStripTopWiredBoundary N n) F]
    rw [hempty N]
    simp
  have hlim := LatticeConfiguration.tendsto_allOpen_of_weak hμ F
  have hconst :
      (fun N : ℕ => horizontalStripTopWiredProbabilityMeasures q n N
        (LatticeConfiguration.allOpen F)) = fun _ => (0 : NNReal) := by
    funext N
    exact hzero N
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end
end PottsContinuity.FKC.Medial
