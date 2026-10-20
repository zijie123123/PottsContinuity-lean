module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceBandStoppingRecords
public import PottsContinuity.Thm3.RSW.StoppingAverage
public import PottsContinuity.Thm3.RSW.StoppedRectangleDualRead
public import PottsContinuity.Thm3.RSW.Lemma4RectangleSource

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.Duality DualityExt Exploration Push RSW
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance routeSixNativeEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The exact complement identity for an edge-defined residual graph. -/
theorem subgraphRemovedEdges_edgeRestriction_eq {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G) :
    subgraphRemovedEdges (edgeRestriction G R) G=R := by
  ext e
  rw [mem_subgraphRemovedEdges,edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff,e.property,true_and,not_not,coe_mem_openEdges_iff]

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
