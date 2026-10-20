module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomCollarLaw
public import PottsContinuity.DualityExt.PositiveInducedSourceBoundaryLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The existing geometric bottom collar realizes exactly the PD bottom-wired
partition. The reused statement contains no probabilistic parameter. -/
theorem bottomCollar_source_partition (a : LatticeVertex) (w h : ℕ) :
    (isolatedExtensionPullbackBoundary
      (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h)
      (frozenBoundary (BoundaryCondition.free ∅)
        (FKC.FiniteFK.rectangleArbitraryBottomCollarState a w h).val)).partition =
    (BoundaryCondition.wired
      {v : RectangleVertex a w h | v.val.2 = a.2}).partition := by
  exact FKC.FiniteFK.rectangleArbitraryBottomCollar_frozen_partition_eq a w h

/-- The bottom-collar inclusion is an embedding of the actual original bonds. -/
theorem bottomCollar_source_map_le (a : LatticeVertex) (w h : ℕ) :
    (rectangleGraph a w h).map
      (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h) ≤
    rectangleGraph (a.1,a.2-1) w (h+1) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

end
end PottsContinuity.RSW
