module

public import PottsContinuity.Exploration.InteriorFreeLaw
public import PottsContinuity.FKC.FiniteFK.FiniteConditionalEventBounds
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Conditional free law on an attained finite selector fibre

The finite stopping-set DMP is usually written as a PMF filtered on the
record event.  This module identifies that conditional PMF with the exact
free law on an embedded graph whenever the record fibre is a frozen-exterior
event and its induced boundary partition is discrete.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open MeasureTheory
open PottsContinuity.PD.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance circuitFiberOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance circuitFiberOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance circuitFiberInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance circuitFiberMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance circuitFiberOuterConfigNonempty : Nonempty (Configuration H) := ⟨∅⟩
local instance circuitFiberConfigMeasurableSpace {U : Type*} (J : SimpleGraph U) :
    MeasurableSpace (Configuration J) := ⊤
local instance circuitFiberConfigMeasurableSingleton {U : Type*} (J : SimpleGraph U) :
    MeasurableSingletonClass (Configuration J) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

private theorem circuitFiber_pmf_toReal_event_eq_expectation
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (E : Set α) :
    (p.toMeasure E).toReal =
      FiniteProbability.expectation p (E.indicator fun _ => (1 : ℝ)) := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · unfold FiniteProbability.expectation
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x ∈ E <;> simp [Set.indicator, h]
  · intro x hx
    by_cases h : x ∈ E
    · simpa [Set.indicator, h] using p.apply_ne_top x
    · simp [Set.indicator, h]

/-- On an attained statistic fibre that is exactly a frozen exterior state,
the conditional PMF pushed to the embedded interior graph is its free FK law
when the pulled-back frozen partition is discrete.  The statement applies to
each record value separately, so it can be used after a concrete finite
stopping-set selector has been constructed. -/
theorem finiteStatisticConditionalPMF_map_embeddedRestriction_eq_free_of_frozenFiber
    (θ : Parameters) (ξ : BoundaryCondition W)
    {β : Type*} (record : Configuration H → β)
    (y : Set.range record)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (hfiber : {C : Configuration H | record C = y.1} =
      frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
    (hfree : ∀ x z : V,
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition.r x z ↔
        x = z) :
    (PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      (law H θ ξ) (fun C => (law_pos H θ ξ C).ne') record y).map
        (embeddedConfigurationRestriction G H f hGH) =
      law G θ (BoundaryCondition.free
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).boundary) := by
  let p := law H θ ξ
  have hcond :
      PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
        p (fun C => (law_pos H θ ξ C).ne') record y =
      p.filter
        (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
        (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K) := by
    apply PMF.ext
    intro C
    simp [PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF,
      p, hfiber]
  calc
    _ = (p.filter
        (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
        (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K)).map
          (embeddedConfigurationRestriction G H f hGH) := by rw [hcond]
    _ = law G θ (BoundaryCondition.free
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).boundary) :=
      law_filter_frozen_map_embeddedRestriction_eq_free_of_discreteBoundary
        f hGH θ ξ K hfree

/-- Free-law comparison for a possibly smaller reference graph. Conditioning
may take place in a wired graph `H`, while the selected interior is embedded
in a separate free graph `J`. This is the volume arrangement used in
`Thm3.Easy.P1ToP2DisconnectionBarrier`, where the conditional wired volume is `Λ_N`
and the comparison free volume is `Λ_M` with `M ≤ N`. -/
theorem finiteStatisticConditionalPMF_embeddedExpectation_le_freeGraph_of_frozenFiber
    {Z : Type*} [Finite Z] {J : SimpleGraph Z}
    (g : V ↪ Z) (hGJ : G.map g ≤ J) (ζ : BoundaryCondition Z)
    (θ : Parameters) (ξ : BoundaryCondition W)
    {β : Type*} (record : Configuration H → β)
    (y : Set.range record)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (hfiber : {C : Configuration H | record C = y.1} =
      frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
    (hfree : ∀ x z : V,
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition.r x z ↔
        x = z)
    (F : Configuration G → ℝ) (hF0 : ∀ C, 0 ≤ F C) (hF : Monotone F) :
    FiniteProbability.expectation
      ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
        (law H θ ξ) (fun C => (law_pos H θ ξ C).ne') record y).map
          (embeddedConfigurationRestriction G H f hGH)) F ≤
    FiniteProbability.expectation (law J θ (BoundaryCondition.free ζ.boundary))
      (fun C => F (embeddedConfigurationRestriction G J g hGJ C)) := by
  rw [finiteStatisticConditionalPMF_map_embeddedRestriction_eq_free_of_frozenFiber
    f hGH θ ξ record y K hfiber hfree]
  exact embedded_free_expectation_le G J g hGJ θ
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).boundary
    ζ.boundary F hF0 hF

/-- Probability comparison with a separate free reference graph for an
increasing event on the embedded interior. The selector record is still an
explicit finite fibre hypothesis; the theorem supplies the conditional-law
and volume-comparison part of the finite-box step of the P1 ⇒ P2 argument. -/
theorem finiteStatisticConditionalPMF_embeddedIncreasingEvent_le_freeGraph_of_frozenFiber
    {Z : Type*} [Finite Z] {J : SimpleGraph Z}
    (g : V ↪ Z) (hGJ : G.map g ≤ J) (ζ : BoundaryCondition Z)
    (θ : Parameters) (ξ : BoundaryCondition W)
    {β : Type*} (record : Configuration H → β)
    (y : Set.range record)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (hfiber : {C : Configuration H | record C = y.1} =
      frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
    (hfree : ∀ x z : V,
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition.r x z ↔
        x = z)
    (A : Set (Configuration G)) (hA : IsUpperSet A) :
    ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      (law H θ ξ) (fun C => (law_pos H θ ξ C).ne') record y).toMeasure
        ((embeddedConfigurationRestriction G H f hGH) ⁻¹' A)).toReal ≤
      ((law J θ (BoundaryCondition.free ζ.boundary)).toMeasure
        ((embeddedConfigurationRestriction G J g hGJ) ⁻¹' A)).toReal := by
  let c := PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
    (law H θ ξ) (fun C => (law_pos H θ ξ C).ne') record y
  let F : Configuration G → ℝ := A.indicator fun _ => 1
  have hF0 : ∀ C, 0 ≤ F C := by
    intro C
    by_cases hC : C ∈ A <;> simp [F, hC]
  have hF : Monotone F := by
    intro C D hCD
    by_cases hC' : C ∈ A
    · have hD : D ∈ A := hA hCD hC'
      simp [F, hC', hD]
    · by_cases hD : D ∈ A <;> simp [F, hC', hD]
  have hExp := finiteStatisticConditionalPMF_embeddedExpectation_le_freeGraph_of_frozenFiber
    f hGH g hGJ ζ θ ξ record y K hfiber hfree F hF0 hF
  have hleft :
      (c.toMeasure ((embeddedConfigurationRestriction G H f hGH) ⁻¹' A)).toReal =
        FiniteProbability.expectation (c.map (embeddedConfigurationRestriction G H f hGH)) F := by
    rw [circuitFiber_pmf_toReal_event_eq_expectation]
    rw [FiniteProbability.expectation_map]
    rfl
  have hright :
      ((law J θ (BoundaryCondition.free ζ.boundary)).toMeasure
        ((embeddedConfigurationRestriction G J g hGJ) ⁻¹' A)).toReal =
        FiniteProbability.expectation (law J θ (BoundaryCondition.free ζ.boundary))
          (fun C => F (embeddedConfigurationRestriction G J g hGJ C)) := by
    rw [circuitFiber_pmf_toReal_event_eq_expectation]
    rfl
  simpa [c] using hleft.le.trans (hExp.trans_eq hright.symm)

end
end PottsContinuity.Exploration
