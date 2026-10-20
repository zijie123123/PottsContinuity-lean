module

public import PottsContinuity.Thm3.RSW.StripBoundaryCylinderLimit
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The exact finite pattern read on original strip bonds. Open and closed
requirements may overlap, in which case the event is empty. -/
def stripRectanglePatternEvent (N n : ℕ)
    (O C : Finset FKC.squareLattice.edgeSet) :
    Set (Configuration (horizontalStripCutRectangle N n)) :=
  {A | O ⊆ A.image (horizontalStripRectangleOriginalEdge N n) ∧
    Disjoint C (A.image (horizontalStripRectangleOriginalEdge N n))}

private theorem pattern_insert_closed (N n : ℕ)
    (O C : Finset FKC.squareLattice.edgeSet) (e : FKC.squareLattice.edgeSet) :
    stripRectanglePatternEvent N n O (insert e C) =
      stripRectanglePatternEvent N n O C \
        stripRectanglePatternEvent N n (insert e O) C := by
  classical
  ext A
  simp only [stripRectanglePatternEvent, Set.mem_ofPred_eq, Set.mem_sdiff,
    Finset.disjoint_insert_left, Finset.insert_subset_iff]
  tauto

private theorem pattern_insert_closed_probability (θ : Parameters) (N n : ℕ)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (O C : Finset FKC.squareLattice.edgeSet) (e : FKC.squareLattice.edgeSet) :
    (measure (horizontalStripCutRectangle N n) θ ξ).real
      (stripRectanglePatternEvent N n O (insert e C)) =
    (measure (horizontalStripCutRectangle N n) θ ξ).real
      (stripRectanglePatternEvent N n O C) -
    (measure (horizontalStripCutRectangle N n) θ ξ).real
      (stripRectanglePatternEvent N n (insert e O) C) := by
  classical
  rw [pattern_insert_closed]
  apply measureReal_sdiff
  · intro A hA
    exact ⟨fun e he => hA.1 (Finset.mem_insert_of_mem he), hA.2⟩
  · exact MeasurableSpace.measurableSet_top
  · exact measure_ne_top _ _

/-- Every finite original-edge pattern loses its lateral-boundary choice.
The conclusion includes closed edges and arbitrary finite patterns, for all
interior edge parameters and all real cluster weights at least one. -/
theorem strip_pattern_boundary_difference_tendsto_zero
    (θ : Parameters) (n K : ℕ)
    (ξ : ∀ N : ℕ, BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (hξ : ∀ N, (ξ N).boundary ⊆ FKC.FiniteFK.horizontalStripTopSidesSet N n)
    (hTop : ∀ N, (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n)).partition ≤
      (ξ N).partition)
    (O C : Finset FKC.squareLattice.edgeSet)
    (hO : ∀ e ∈ O, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n))
    (hC : ∀ e ∈ C, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    Tendsto (fun N =>
      (measure (horizontalStripCutRectangle N n) θ (ξ N)).real
        (stripRectanglePatternEvent N n O C) -
      (measure (horizontalStripCutRectangle N n) θ
        (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n))).real
        (stripRectanglePatternEvent N n O C)) atTop (𝓝 0) := by
  classical
  induction C using Finset.induction_on generalizing O with
  | empty =>
    simpa only [stripRectanglePatternEvent, Finset.disjoint_empty_left, and_true,
      horizontalStripRectangleCylinderEvent, Measure.real] using
      strip_cylinder_boundary_difference_tendsto_zero θ n K ξ hξ hTop O hO
  | @insert e C he ih =>
    have hC' : ∀ f ∈ C, f ∈ Set.range (horizontalStripRectangleOriginalEdge K n) :=
      fun f hf => hC f (Finset.mem_insert_of_mem hf)
    have hO' : ∀ f ∈ insert e O, f ∈ Set.range (horizontalStripRectangleOriginalEdge K n) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hC f (Finset.mem_insert_self f C)
      · exact hO f hf
    have h := (ih O hO hC').sub (ih (insert e O) hO' hC')
    simp only [sub_zero] at h
    convert h using 1
    funext N
    rw [pattern_insert_closed_probability, pattern_insert_closed_probability]
    ring

end
end PottsContinuity.RSW
