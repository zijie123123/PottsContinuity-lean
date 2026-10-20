module

public import PottsContinuity.Thm3.Push.EmbeddedRemainingGraph
public import PottsContinuity.Thm3.Push.EmbeddedFrontierWiring
public import PottsContinuity.Thm3.Push.EmbeddedFilledDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance outerFrontierEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The actual OUTER remaining FK law dominates the reference active law
wired on its proved frontier. Exterior vertices and bonds stay in the outer
law, and its original boundary partition is retained in the induced frozen
partition. No random-domain containment or additional locality premise is used. -/
theorem frontier_wired_le_outer_frozen_restriction {V : Type*} [Finite V]
    (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v))
    (E : Set (Configuration (activeUnexaminedGraph (rectangleGraph a w h)
      (rectangleFilledTopReveal a w h (embeddedConfigurationRestriction _ _ f hRG A)))))
    (hE : IsUpperSet E) :
    let D := embeddedConfigurationRestriction _ _ f hRG A
    let R := rectangleFilledTopReveal a w h D
    let Rout := embeddedFilledTopReveal a w h G f hRG A
    (measure (activeUnexaminedGraph (rectangleGraph a w h) R) θ
      (BoundaryCondition.wired {x | x.val ∈ filledFrontierWiredVertices a w h D}) E).toReal ≤
    (measure (edgeRestriction G Rout) θ (frozenBoundary ξ (A ∩ Rout))
      {C | embeddedConfigurationRestriction _ _ ((Function.Embedding.subtype _).trans f)
        (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG R) C ∈ E}).toReal := by
  let D := embeddedConfigurationRestriction _ _ f hRG A
  let R := rectangleFilledTopReveal a w h D
  let Rout := embeddedFilledTopReveal a w h G f hRG A
  let ξf := frozenBoundary ξ (A ∩ Rout)
  let j : unexaminedVertices (rectangleGraph a w h) R ↪ V :=
    (Function.Embedding.subtype _).trans f
  let : Finite (unexaminedVertices (rectangleGraph a w h) R) := by
    change Finite {x : RectangleVertex a w h // x ∈ unexaminedVertices (rectangleGraph a w h) R}
    infer_instance
  have hpart := embedded_frontier_wiring_le_actual_frozen a w h G f hRG A hA ξ hsides
  have hactive :
      (BoundaryCondition.wired {x : unexaminedVertices (rectangleGraph a w h) R |
        x.val ∈ filledFrontierWiredVertices a w h D}).partition ≤
      (isolatedExtensionPullbackBoundary j ξf).partition := by
    intro x y hxy
    change ξf.partition.r (j x) (j y)
    rcases hxy with rfl | ⟨hx,hy⟩
    · exact ξf.partition.refl _
    · exact hpart (Or.inr ⟨hx,hy⟩)
  exact (measure_boundary_comparison θ _ _ hactive E hE).trans
    (RSW.embedded_boundary_probability_le _ _ j
      (activeUnexaminedGraph_map_le_outer_remaining (rectangleGraph a w h) G f hRG R) θ ξf E hE)

end
end PottsContinuity.Push
