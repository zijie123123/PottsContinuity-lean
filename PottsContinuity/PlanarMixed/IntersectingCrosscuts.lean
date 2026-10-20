module

public import PottsContinuity.PlanarMixed.CrosscutOpenWalks
public import PottsContinuity.PD.FK.ConditionalLaw

/-! The intersecting-crosscut branch of the source conditioned estimate.
Actual open intersections connect the original endpoints, hence the source
target has conditional probability one on every compatible frozen record.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance intersectingCrosscutEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Intersecting actual open walks connect their original starting vertices. -/
theorem openWalks_intersection_actualConnected {V : Type*}
    (G : SimpleGraph V) (K : Configuration G) {a b t u : V}
    (p : (openGraph G K).Walk a t) (q : (openGraph G K).Walk b u)
    (hinter : ∃ z, z ∈ p.support ∧ z ∈ q.support) : ActualConnected G K a b := by
  obtain ⟨z, hzp, hzq⟩ := hinter
  exact (openWalk_support_actualConnected G K p p.start_mem_support hzp).trans
    (openWalk_support_actualConnected G K q hzq q.start_mem_support)

end
end PottsContinuity.PlanarMixed
