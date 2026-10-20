module

public import PottsContinuity.Thm3.RSW.StripBoundaryCylinderError
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Every actual increasing original-edge cylinder is raised by admissible
additional boundary identifications. No support restriction is needed. -/
theorem strip_cylinder_topOnly_le_boundary
    (θ : Parameters) (N n : ℕ)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (hTop : (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n)).partition ≤ ξ.partition)
    (F : Finset FKC.squareLattice.edgeSet) :
    (measure (horizontalStripCutRectangle N n) θ
      (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n))
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
    (measure (horizontalStripCutRectangle N n) θ ξ
      (horizontalStripRectangleCylinderEvent N n F)).toReal := by
  apply measure_boundary_comparison θ _ ξ hTop
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

/-- Original finite-cylinder probabilities lose their lateral-boundary
choice at fixed strip height, uniformly over EVERY admissible boundary sequence.
This is an actual vanishing difference, not an assumed common weak limit. -/
theorem strip_cylinder_boundary_difference_tendsto_zero
    (θ : Parameters) (n K : ℕ)
    (ξ : ∀ N : ℕ, BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (hξ : ∀ N, (ξ N).boundary ⊆ FKC.FiniteFK.horizontalStripTopSidesSet N n)
    (hTop : ∀ N, (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n)).partition ≤
      (ξ N).partition)
    (F : Finset FKC.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    Tendsto (fun N =>
      (measure (horizontalStripCutRectangle N n) θ (ξ N)
        (horizontalStripRectangleCylinderEvent N n F)).toReal -
      (measure (horizontalStripCutRectangle N n) θ
        (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n))
        (horizontalStripRectangleCylinderEvent N n F)).toReal) atTop (𝓝 0) := by
  have hlo : ∀ N, 0 ≤
      (measure (horizontalStripCutRectangle N n) θ (ξ N)
        (horizontalStripRectangleCylinderEvent N n F)).toReal -
      (measure (horizontalStripCutRectangle N n) θ
        (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n))
        (horizontalStripRectangleCylinderEvent N n F)).toReal := by
    intro N
    exact sub_nonneg.mpr (strip_cylinder_topOnly_le_boundary θ N n (ξ N) (hTop N) F)
  have hup : ∀ᶠ N : ℕ in atTop,
      (measure (horizontalStripCutRectangle N n) θ (ξ N)
        (horizontalStripRectangleCylinderEvent N n F)).toReal -
      (measure (horizontalStripCutRectangle N n) θ
        (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n))
        (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      (measure (horizontalStripCutRectangle N n) θ (ξ N)
        (horizontalStripClosedCutFailureEvent N n K)).toReal := by
    filter_upwards [eventually_ge_atTop K] with N hN
    have hb := strip_cylinder_boundary_le_topOnly_add_failure hN θ (ξ N) (hξ N) (hTop N) F hF
    linarith only [hb]
  apply squeeze_zero' (Eventually.of_forall hlo) hup
  exact strip_closed_cut_failure_tendsto_zero θ n K ξ

end
end PottsContinuity.RSW
