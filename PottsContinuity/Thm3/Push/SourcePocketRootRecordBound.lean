module

public import PottsContinuity.Thm3.Push.SourcePocketObservedRoots

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourcePocketRootRecordBoundEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The conditional estimate connects the original physical source roots,
with deterministic record locality as its only exploration premise. -/
theorem sourcePocket_original_roots_lower_bound_of_recordLocality
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
        {ω | ActualConnected H ω (j P.firstStart) (j P.secondStart)}).toReal := by
  let μ := (law H (criticalParameters q) ξ).filter (revealRecordEvent reveal C) (by
    rw [revealRecordEvent_eq_frozenStateEvent reveal hlocal C]
    exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))
  have hb := sourcePocket_revealRecord_lower_bound_of_recordLocality w h x P H j hSH
    hgeometry q ξ reveal hlocal C hcarrier Q hp hq
  apply hb.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply μ.toMeasure_mono MeasurableSpace.measurableSet_top
  intro ω hω
  have hrec := (PMF.mem_support_filter_iff _).mp hω.2 |>.1
  rw [revealRecordEvent_eq_frozenStateEvent reveal hlocal C] at hrec
  exact sourcePocket_observed_roots_of_active_connection w h x P H j hSH reveal C ω
    hcarrier Q hp hq hrec hω.1

end
end PottsContinuity.Push
