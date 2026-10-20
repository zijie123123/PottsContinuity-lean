module

public import PottsContinuity.Thm3.Push.SourcePocketFrozenBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourcePocketRecordBoundEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A genuine stable source record inherits the augmented crossing bound.
The only exploration hypothesis is the exact deterministic record locality;
all FK and boundary-comparison inputs are discharged. -/
theorem sourcePocket_revealRecord_lower_bound_of_recordLocality
    (w h : ℕ) (x : ℤ) (P : SourceWalkPair (rectangleGraph (0,0) w h))
    {U : Type*} [Finite U] (H : SimpleGraph U)
    (j : RectangleVertex (0,0) w h ↪ U) (hSH : (rectangleGraph (0,0) w h).map j ≤ H)
    (hgeometry : RetainedRectanglePathGeometry w h x P) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition U) (reveal : RevealMap (G := H))
    (hlocal : ∀ C D, D ∩ reveal C = C ∩ reveal C → reveal D = reveal C)
    (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H)
    (Q : SourceWalkPair (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)))
    (hp : ∀ z, z ∈ Q.first.support ↔ z ∈ P.first.support)
    (hq : ∀ z, z ∈ Q.second.support ↔ z ∈ P.second.support) :
    1/(1+(q:ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter (revealRecordEvent reveal C)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hlocal C]
          exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure
        {ω | embeddedConfigurationRestriction (sourcePocketActiveGraph w h x P) H j
          ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH) ω ∈
          arcsConnectionEvent (sourcePocketActiveGraph w h x P)
            {z | z ∈ P.first.support} {z | z ∈ P.second.support}}).toReal := by
  have hb := sourcePocket_record_conditional_lower_bound w h x P H j hSH hgeometry q ξ reveal C hcarrier Q hp hq
  simpa only [revealRecordEvent_eq_frozenStateEvent reveal hlocal C,
    sourcePocketRecordedConfiguration,frozenStateEvent,← hcarrier] using hb

end
end PottsContinuity.Push
