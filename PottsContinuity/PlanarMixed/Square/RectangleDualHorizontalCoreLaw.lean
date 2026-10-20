/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualHorizontalCoreLaw.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDualHorizontalCore
public import PottsContinuity.PD.FK.EmbeddedMarginalLaw
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial
noncomputable section

local instance rectangleDualHorizontalCoreLawOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _
local instance rectangleDualHorizontalCoreLawInnerEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualHorizontalCoreGraph a w h).edgeSet := Classical.decEq _
local instance rectangleDualHorizontalCoreLawMappedEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq ((rectangleDualHorizontalCoreGraph a w h).map
      (rectangleDualHorizontalCoreInclusion a w h)).edgeSet := Classical.decEq _

theorem rectangleDualHorizontalCoreGraph_map_le
    (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualHorizontalCoreGraph a w h).map
        (rectangleDualHorizontalCoreInclusion a w h) ≤
      rectangleDualGraph a w h := by
  intro u v huv
  obtain ⟨u₀, v₀, huv₀, rfl, rfl⟩ :=
    (SimpleGraph.map_adj _ _ _ _).mp huv
  change (rectangleDualGraph a w h).Adj u₀.1 v₀.1 at huv₀
  exact huv₀

theorem rectangleDualHorizontalCoreGraph_law_map
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) (q : Parameters) :
    (law (rectangleDualGraph a w h) q
      (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h))).map
        (embeddedConfigurationRestriction
          (rectangleDualHorizontalCoreGraph a w h)
          (rectangleDualGraph a w h)
          (rectangleDualHorizontalCoreInclusion a w h)
          (rectangleDualHorizontalCoreGraph_map_le a w h)) =
      law (rectangleDualHorizontalCoreGraph a w h) q
        (BoundaryCondition.wired
          {u : rectangleDualHorizontalCoreVertex a w h |
            rectangleDualHorizontalCoreInclusion a w h u ∈
              rectangleDoubleCollarDualInnerVerticalSides a w h}) := by
  classical
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact rectangleDualHorizontalCore_boundary_retraction a w h hh K

end
end PottsContinuity.PlanarMixed.Square
