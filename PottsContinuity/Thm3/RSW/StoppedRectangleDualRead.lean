module

public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.Thm3.RSW.RectangleSubgraphDualEdges
public import PottsContinuity.DualityExt.PositiveConditionedSubgraphDuality

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

/-- Read exactly the remaining original sampled bonds and complement them
into the actual residual dual graph, retaining its full host vertex carrier. -/
def rectangleRecordDualRead {a : LatticeVertex} {w h : ℕ}
    {X : Type*} [Finite X] (J : SimpleGraph X)
    (f : X ↪ RectangleVertex a w h) (hJ : J.map f ≤ rectangleGraph a w h)
    (C : Configuration (rectangleGraph a w h)) :
    Configuration (rectangleSubgraphDualGraph hJ) :=
  (rectangleSubgraphDualConfigurationEquiv hJ)
    (isolatedExtensionConfigurationEquiv J f
      (embeddedConfigurationRestriction J (rectangleGraph a w h) f hJ C))

/-- Every retained dual bond reads the complementary state of its unique
original sampled bond in the full source sample. -/
theorem rectangleRecordDualRead_mem {a : LatticeVertex} {w h : ℕ}
    {X : Type*} [Finite X] (J : SimpleGraph X)
    (f : X ↪ RectangleVertex a w h) (hJ : J.map f ≤ rectangleGraph a w h)
    (C : Configuration (rectangleGraph a w h)) (e : J.edgeSet) :
    rectangleSubgraphSourceDualEdge hJ (isolatedExtensionEdgeEquiv J f e) ∈
      rectangleRecordDualRead J f hJ C ↔ embeddedEdgeEmbedding J (rectangleGraph a w h) f hJ e ∉ C := by
  have h₁ := rectangleSubgraphSourceDualEdge_mem hJ
    (isolatedExtensionConfigurationEquiv J f
      (embeddedConfigurationRestriction J (rectangleGraph a w h) f hJ C))
    (isolatedExtensionEdgeEquiv J f e)
  have h₂ : isolatedExtensionEdgeEquiv J f e ∈
      isolatedExtensionConfigurationEquiv J f
        (embeddedConfigurationRestriction J (rectangleGraph a w h) f hJ C) ↔
      e ∈ embeddedConfigurationRestriction J (rectangleGraph a w h) f hJ C :=
    Finset.mem_map' (isolatedExtensionEdgeEquiv J f).toEmbedding
  exact h₁.trans ((not_congr h₂).trans
    (not_congr (mem_embeddedConfigurationRestriction J (rectangleGraph a w h) f hJ C e)))

end
end PottsContinuity.RSW
