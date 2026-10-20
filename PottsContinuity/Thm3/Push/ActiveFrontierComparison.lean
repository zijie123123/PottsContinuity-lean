module

public import PottsContinuity.Thm3.Push.ActiveFrontierBoundary
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterComparison
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance activeComparisonEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The original top/side-wired rectangle, restricted to its active lower
bonds, is dominated by wiring the ACTUAL filled frontier. All closure and
original-boundary avoidance conditions have been proved for this exploration. -/
theorem reference_active_restriction_le_frontier_wired
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h) (θ : Parameters)
    (E : Set (Configuration (activeUnexaminedGraph (rectangleGraph a w h)
      (rectangleFilledTopReveal a w h A)))) (hE : IsUpperSet E) :
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)})
      {B | embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le _ _) B ∈ E}).toReal ≤
    (measure (activeUnexaminedGraph (rectangleGraph a w h) (rectangleFilledTopReveal a w h A)) θ
      (BoundaryCondition.wired {x | x.val ∈ filledFrontierWiredVertices a w h A}) E).toReal := by
  apply embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _) θ _ _ ?_ ?_ E hE
  · intro x hx y hxy
    exact active_filledFrontier_neighbor_closed a w h A hA hx hxy
  · intro x hx
    exact active_filledFrontier_boundary_avoid a w h A hA hx

/-- Inclusion into the graph of all remaining original bonds. Only isolated
vertices are omitted; no sampled edge or path is replaced by a virtual edge. -/
theorem activeUnexaminedGraph_map_le_edgeRestriction {V : Type*} (G : SimpleGraph V)
    (R : Configuration G) :
    (activeUnexaminedGraph G R).map (Function.Embedding.subtype _) ≤ edgeRestriction G R := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

end
end PottsContinuity.Push
