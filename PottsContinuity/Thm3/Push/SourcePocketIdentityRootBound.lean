module

public import PottsContinuity.Thm3.Push.SourcePocketRootRecordBound
public import PottsContinuity.Thm3.Push.SourceIdentityRestriction

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourcePocketIdentityRootEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The exact deleted-edge complement is the original revealed carrier. -/
theorem subgraphRemovedEdges_edgeRestriction_eq {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G) :
    subgraphRemovedEdges (edgeRestriction G R) G = R := by
  classical
  ext e
  rw [mem_subgraphRemovedEdges,edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff,e.property,true_and,not_not,coe_mem_openEdges_iff]

/-- The physical original-root estimate directly on the original source
sample. No identity-restriction or complement-carrier premise is needed. -/
theorem sourcePocket_source_roots_lower_bound_of_recordLocality
    (w h : ℕ) (x : ℤ) (P : SourceWalkPair (rectangleGraph (0,0) w h))
    (hgeometry : RetainedRectanglePathGeometry w h x P) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition (RectangleVertex (0,0) w h)) (reveal : RevealMap (G := rectangleGraph (0,0) w h))
    (hlocal : ∀ C D, D ∩ reveal C = C ∩ reveal C → reveal D = reveal C)
    (C : Configuration (rectangleGraph (0,0) w h))
    (hcarrier : reveal C = pocketAugmentedSourceReveal w h x P.secondEnd.val.2
      (Subtype.val '' {z | z ∈ P.first.support}) (Subtype.val '' {z | z ∈ P.second.support}))
    (Q : SourceWalkPair (openGraph (rectangleGraph (0,0) w h)
      C))
    (hp : ∀ z, z ∈ Q.first.support ↔ z ∈ P.first.support)
    (hq : ∀ z, z ∈ Q.second.support ↔ z ∈ P.second.support) :
    1/(1+(q:ℝ)^2) ≤
      (((law (rectangleGraph (0,0) w h) (criticalParameters q) ξ).filter (revealRecordEvent reveal C)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hlocal C]
          exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure
        {ω | ActualConnected (rectangleGraph (0,0) w h) ω P.firstStart P.secondStart}).toReal := by
  let G := rectangleGraph (0,0) w h
  let j := Function.Embedding.refl (RectangleVertex (0,0) w h)
  let hGG := sourceIdentity_map_le G
  let f : openGraph G C →g openGraph G (embeddedConfigurationRestriction G G j hGG C) := {
    toFun := id
    map_rel' := by
      intro a b hab
      change (openGraph G (embeddedConfigurationRestriction G G (Function.Embedding.refl _)
        (sourceIdentity_map_le G) C)).Adj a b
      rw [embeddedConfigurationRestriction_sourceIdentity]
      exact hab }
  let T : SourceWalkPair (openGraph G (embeddedConfigurationRestriction G G j hGG C)) := {
    firstStart := Q.firstStart
    secondStart := Q.secondStart
    firstEnd := Q.firstEnd
    secondEnd := Q.secondEnd
    first := Q.first.map f
    second := Q.second.map f }
  have hpT : ∀ z, z ∈ T.first.support ↔ z ∈ P.first.support := by
    intro z
    change z ∈ (Q.first.map f).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    change z ∈ Q.first.support.map id ↔ _
    rw [List.map_id]
    exact hp z
  have hqT : ∀ z, z ∈ T.second.support ↔ z ∈ P.second.support := by
    intro z
    change z ∈ (Q.second.map f).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    change z ∈ Q.second.support.map id ↔ _
    rw [List.map_id]
    exact hq z
  have hc : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) G := by
    change reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map id) G
    rw [SimpleGraph.map_id]
    rw [sourcePocketActiveGraph,subgraphRemovedEdges_edgeRestriction_eq]
    exact hcarrier
  exact sourcePocket_original_roots_lower_bound_of_recordLocality w h x P G j hGG
    hgeometry q ξ reveal hlocal C hc T hpT hqT

end
end PottsContinuity.Push
