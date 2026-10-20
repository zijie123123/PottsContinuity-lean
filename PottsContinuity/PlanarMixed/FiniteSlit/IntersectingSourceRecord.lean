module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRecordGeometry
public import PottsContinuity.PlanarMixed.IntersectingCrosscuts

/-! The intersecting-arm alternative for the literal source restriction. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance intersectingSourceRecordEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Actual open source arms with a common vertex and roots in the marked sets.
There is no disjointness, ordering, height, or planar-separation premise. -/
structure IntersectingSourceArms {W : Type*} (S : SimpleGraph W)
    (C : Configuration S) (I J : Set W) where
  firstStart : W
  secondStart : W
  firstEnd : W
  secondEnd : W
  first : (openGraph S C).Walk firstStart firstEnd
  second : (openGraph S C).Walk secondStart secondEnd
  first_in : firstStart ∈ I
  second_in : secondStart ∈ J
  intersect : ∃ z, z ∈ first.support ∧ z ∈ second.support

/-- Intersecting arms give an actual sampled connection between their roots. -/
theorem IntersectingSourceArms.connects {W : Type*} {S : SimpleGraph W}
    {C : Configuration S} {I J : Set W} (D : IntersectingSourceArms S C I J) :
    C ∈ arcsConnectionEvent S I J :=
  ⟨D.firstStart,D.first_in,D.secondStart,D.second_in,
    openWalks_intersection_actualConnected S C D.first D.second D.intersect⟩

variable {W U : Type*} [Finite W] [Finite U]
  {S : SimpleGraph W} {H : SimpleGraph U} {j : W ↪ U} {hSH : S.map j ≤ H}
  {I J : Set W}

end
end PottsContinuity.PlanarMixed.FiniteSlit
