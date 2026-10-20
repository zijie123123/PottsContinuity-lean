module

public import PottsContinuity.Thm3.Push.BottomCoreBoundary
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.Square
noncomputable section

/-- The retained core is an actual induced subgraph of the true dual. -/
theorem bottomCoreGraph_map_le (a : LatticeVertex) (w h : ℕ) :
    (generalRectangleDualBottomCoreGraph a w h).map (bottomCoreInclusion a w h) ≤
      rectangleDualGraph a w h := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

/-- Integrating all free bottom leaves gives exactly the retained-core law.
The parameter is the unrestricted admissible PD record; no upper bound on
the cluster weight or source-partition premise is used. -/
theorem bottomCore_law_map (a : LatticeVertex) (w h : ℕ) (θ : Parameters) :
    (law (rectangleDualGraph a w h) θ
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h))).map
      (embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
        (rectangleDualGraph a w h) (bottomCoreInclusion a w h) (bottomCoreGraph_map_le a w h)) =
    law (generalRectangleDualBottomCoreGraph a w h) θ
      (BoundaryCondition.wired {u : generalRectangleDualBottomCoreVertex a w h |
        bottomCoreInclusion a w h u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h}) := by
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact bottomCoreBoundary_partition a w h K

end
end PottsContinuity.Push
