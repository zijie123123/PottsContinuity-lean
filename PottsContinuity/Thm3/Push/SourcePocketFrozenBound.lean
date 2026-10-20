module

public import PottsContinuity.Thm3.Push.SourcePocketActiveBound
public import PottsContinuity.PlanarMixed.FiniteSlit.SupportRecordWalks

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourcePocketFrozenEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

variable (w h : ℕ) (x : ℤ) (P : SourceWalkPair (rectangleGraph (0,0) w h))
    {U : Type*} [Finite U] (H : SimpleGraph U)
    (j : RectangleVertex (0,0) w h ↪ U) (hSH : (rectangleGraph (0,0) w h).map j ≤ H)

/-- Actual support-coherent sampled walks induce both path classes in the
recorded frozen partition for the augmented source reveal. -/
theorem sourcePocketSupportPaths_recorded_boundary_order
    (hgeometry : RetainedRectanglePathGeometry w h x P)
    (ξ : BoundaryCondition U) (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H)
    (Q : SourceWalkPair (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)))
    (hp : ∀ z, z ∈ Q.first.support ↔ z ∈ P.first.support)
    (hq : ∀ z, z ∈ Q.second.support ↔ z ∈ P.second.support) :
    (sourceSeparatePathBoundary w h x P hgeometry).partition ≤
      (isolatedExtensionPullbackBoundary j
        (frozenBoundary ξ (revealRecordConfiguration reveal C).val)).partition := by
  let R := pocketAugmentedSourceReveal w h x P.secondEnd.val.2
    (Subtype.val '' {z | z ∈ P.first.support}) (Subtype.val '' {z | z ∈ P.second.support})
  have hpR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ Q.first.edges → e ∈ R :=
    fun e he => sourceExteriorReveal_subset_pocketAugmented _ _ _ _ _ _ (sourceSupportWalk_bond_exposed w h x P Q.first
      (Or.inl (fun z hz => (hp z).mp hz)) e he)
  have hqR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ Q.second.edges → e ∈ R :=
    fun e he => sourceExteriorReveal_subset_pocketAugmented _ _ _ _ _ _ (sourceSupportWalk_bond_exposed w h x P Q.second
      (Or.inr (fun z hz => (hq z).mp hz)) e he)
  let p := recordedSourceOpenWalk w h H j hSH R reveal C hcarrier Q.first hpR
  let q := recordedSourceOpenWalk w h H j hSH R reveal C hcarrier Q.second hqR
  have hpS : p.support = Q.first.support := recordedSourceOpenWalk_support w h H j hSH R reveal C hcarrier Q.first hpR
  have hqS : q.support = Q.second.support := recordedSourceOpenWalk_support w h H j hSH R reveal C hcarrier Q.second hqR
  apply twoBlockBoundary_le_pullback_frozen_of_arcConnections H j ξ _
    {z | z ∈ P.first.support} {z | z ∈ P.second.support} hgeometry.supports_disjoint
  · intro a ha b hb
    have ha' : a ∈ p.support := hpS.symm ▸ (hp a).mpr ha
    have hb' : b ∈ p.support := hpS.symm ▸ (hp b).mpr hb
    obtain ⟨s⟩ := openWalk_support_actualConnected _ _ p ha' hb'
    exact ⟨s.map (embeddedOpenRestrictionHom _ H j hSH _)⟩
  · intro a ha b hb
    have ha' : a ∈ q.support := hqS.symm ▸ (hq a).mpr ha
    have hb' : b ∈ q.support := hqS.symm ▸ (hq b).mpr hb
    obtain ⟨s⟩ := openWalk_support_actualConnected _ _ q ha' hb'
    exact ⟨s.map (embeddedOpenRestrictionHom _ H j hSH _)⟩

/-- The exact source conditional law inherits the canonical augmented
crossing bound whenever its frozen partition contains the two path classes. -/
theorem sourcePocket_conditional_lower_of_frozenBoundaryDomination
    (hgeometry : RetainedRectanglePathGeometry w h x P) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition U)
    (K : RemovedConfiguration H (subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H))
    (hpart : (sourceSeparatePathBoundary w h x P hgeometry).partition ≤
      (isolatedExtensionPullbackBoundary j (frozenBoundary ξ K.val)).partition) :
    1/(1+(q:ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter
        (frozenStateEvent (subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H) K)
        (frozenStateEvent_support _ _ _ K)).toMeasure
        {C | embeddedConfigurationRestriction (sourcePocketActiveGraph w h x P) H j
          ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH) C ∈
          arcsConnectionEvent (sourcePocketActiveGraph w h x P)
            {z | z ∈ P.first.support} {z | z ∈ P.second.support}}).toReal := by
  have hlaw := law_filter_frozen_map_embeddedRestriction (sourcePocketActiveGraph w h x P)
    H j ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH)
    (criticalParameters q) ξ K
  have hprob := congrArg (fun μ : PMF (Configuration (sourcePocketActiveGraph w h x P)) =>
    (μ.toMeasure (arcsConnectionEvent _ {z | z ∈ P.first.support} {z | z ∈ P.second.support})).toReal) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hprob
  have hb := (source_pocketAugmented_separate_wired_paths_lower_bound w h x P hgeometry q).trans
    (measure_boundary_comparison (criticalParameters q) _ _ hpart _ (arcsConnectionEvent_isUpperSet _ _))
  exact hb.trans_eq hprob.symm

/-- The actual revealed state, on the fixed complement of the augmented
source graph. The carrier equality is used only to type its support. -/
def sourcePocketRecordedConfiguration
    (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H) :
    RemovedConfiguration H (subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H) :=
  ⟨(revealRecordConfiguration reveal C).val,by
    rw [← hcarrier]
    exact (revealRecordConfiguration reveal C).property⟩

/-- The conditional bound at an actual source record needs neither a
partition-comparison premise nor a conditional-law premise: observed
support-coherent open walks discharge both wired path classes. -/
theorem sourcePocket_record_conditional_lower_bound
    (hgeometry : RetainedRectanglePathGeometry w h x P) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition U) (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H)
    (Q : SourceWalkPair (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)))
    (hp : ∀ z, z ∈ Q.first.support ↔ z ∈ P.first.support)
    (hq : ∀ z, z ∈ Q.second.support ↔ z ∈ P.second.support) :
    let K := sourcePocketRecordedConfiguration w h x P H j reveal C hcarrier
    1/(1+(q:ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter
        (frozenStateEvent (subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H) K)
        (frozenStateEvent_support _ _ _ K)).toMeasure
        {ω | embeddedConfigurationRestriction (sourcePocketActiveGraph w h x P) H j
          ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH) ω ∈
          arcsConnectionEvent (sourcePocketActiveGraph w h x P)
            {z | z ∈ P.first.support} {z | z ∈ P.second.support}}).toReal := by
  dsimp only
  apply sourcePocket_conditional_lower_of_frozenBoundaryDomination w h x P H j hSH hgeometry q
  exact sourcePocketSupportPaths_recorded_boundary_order w h x P H j hSH hgeometry ξ reveal C
    hcarrier Q hp hq

end
end PottsContinuity.Push
