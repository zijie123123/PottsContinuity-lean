-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedMarginalLaw
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomWiredDuality

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance generalDualCoreLawOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _
local instance generalDualCoreLawInnerEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCoreGraph a w h).edgeSet := Classical.decEq _
local instance generalDualCoreLawMappedEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq ((generalRectangleDualBottomCoreGraph a w h).map
      (generalRectangleDualBottomCoreInclusion a w h)).edgeSet := Classical.decEq _

/-- The retained true-dual core embeds as an actual subgraph of the inner
true dual graph, with its full induced vertex set. -/
theorem generalRectangleDualBottomCoreGraph_map_le
    (a : LatticeVertex) (w h : ℕ) :
    (generalRectangleDualBottomCoreGraph a w h).map
        (generalRectangleDualBottomCoreInclusion a w h) ≤
      rectangleDualGraph a w h := by
  intro u v huv
  obtain ⟨u₀, v₀, huv₀, rfl, rfl⟩ :=
    (SimpleGraph.map_adj _ _ _ _).mp huv
  change (rectangleDualGraph a w h).Adj u₀.1 v₀.1 at huv₀
  exact huv₀

/-- The actual three-side-wired dual law, restricted to its induced bottom core,
is exactly the FK law with the retained three-side wiring. -/
theorem generalRectangleDualBottomCoreGraph_law_map
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight) :
    (law (rectangleDualGraph a w h) q
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h))).map
        (embeddedConfigurationRestriction
          (generalRectangleDualBottomCoreGraph a w h)
          (rectangleDualGraph a w h)
          (generalRectangleDualBottomCoreInclusion a w h)
          (generalRectangleDualBottomCoreGraph_map_le a w h)) =
      law (generalRectangleDualBottomCoreGraph a w h) q
        (BoundaryCondition.wired
          {u : generalRectangleDualBottomCoreVertex a w h |
            (generalRectangleDualBottomCoreInclusion a w h u) ∈
              generalRectangleDualBottomCollarInnerThreeSides a w h}) := by
  classical
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact generalRectangleDualBottomCoreBoundary_retraction a w h K

end
end PottsContinuity.FKC.FiniteFK
