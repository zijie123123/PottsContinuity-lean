module

public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Endpoint-only dual laws for rectangular subgraphs

The rectangle conditioning proof keeps the full host dual vertex carrier.
This module removes isolated dual vertices and transfers the exact law to the
source-style graph whose vertices are precisely the endpoints of retained dual
edges.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {G : SimpleGraph (RectangleVertex a w h)}

/-- Positive-`q` free duality on a rectangle subgraph, now carried by exactly
the endpoints of the retained dual edges. Its boundary partition is the
pullback of the rectangle exterior wiring and the forced-open deleted dual
bonds; isolated host dual vertices contribute only a cancelling common factor. -/
theorem positive_free_subgraph_endpoint_duality_law
    (hG : G ≤ rectangleGraph a w h)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    (positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free ∅)).map
        ((rectangleSubgraphDualConfigurationEquiv hG).trans
          (positiveActiveConfigurationEquiv (rectangleSubgraphDualGraph hG)).symm) =
      positiveFKLaw (positiveActiveGraph (rectangleSubgraphDualGraph hG))
        q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
        (isolatedExtensionPullbackBoundary
          (positiveActiveInclusion (rectangleSubgraphDualGraph hG))
          (frozenBoundary (rectangleDualBoundaryCondition a w h)
            (rectangleSubgraphRemovedDualEdges hG))) := by
  let H := rectangleSubgraphDualGraph hG
  let η := frozenBoundary (rectangleDualBoundaryCondition a w h)
    (rectangleSubgraphRemovedDualEdges hG)
  let e₁ := rectangleSubgraphDualConfigurationEquiv hG
  let e₂ := positiveActiveConfigurationEquiv H
  have hdual := positive_free_subgraph_duality_law hG hq hp hp1
  have hactive := positiveFKLaw_activeGraph_map_boundary_pullback H hq
    (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1) η
  have hback :
      (positiveFKLaw H q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1) η).map
          e₂.symm =
        positiveFKLaw (positiveActiveGraph H) q (dualParameter q p) hq
          (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
          (isolatedExtensionPullbackBoundary (positiveActiveInclusion H) η) := by
    calc
      _ = ((positiveFKLaw (positiveActiveGraph H) q (dualParameter q p) hq
          (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
          (isolatedExtensionPullbackBoundary (positiveActiveInclusion H) η)).map e₂).map
            e₂.symm := by
              exact congrArg (fun μ : PMF (Configuration H) => μ.map e₂.symm)
                hactive.symm
      _ = _ := by
        rw [PMF.map_comp]
        have hcomp : e₂.symm ∘ e₂ = id := by
          funext A
          exact Equiv.symm_apply_apply e₂ A
        rw [hcomp, PMF.map_id]
  calc
    _ = ((positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free ∅)).map e₁).map e₂.symm := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [hdual, hback]

end
end PottsContinuity.DualityExt
