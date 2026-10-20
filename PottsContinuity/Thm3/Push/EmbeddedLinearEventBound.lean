module

public import PottsContinuity.PD.FK.EmbeddedMarginalLaw
public import PottsContinuity.PD.RCInfinite.FiniteConditioning
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- A common linear event inequality for every finite conditional law holds
for their genuine mixture, with no independence or single-law identification. -/
theorem pmf_bind_event_linear_bound {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (κ : α → PMF β) (E F : Set β) (c : ℝ)
    (h : ∀ a, c*((κ a).toMeasure E).toReal ≤ ((κ a).toMeasure F).toReal) :
    c*((p.bind κ).toMeasure E).toReal ≤ ((p.bind κ).toMeasure F).toReal := by
  simp only [PD.RCInfinite.pmf_measureReal_eq_expectation] at h ⊢
  rw [FiniteProbability.expectation_bind,FiniteProbability.expectation_bind]
  unfold FiniteProbability.expectation at h ⊢
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ = (p a).toReal * (c * ∑ b, (κ a b).toReal * E.indicator (fun _ => (1 : ℝ)) b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

/-- A finite FK event inequality valid for EVERY inner boundary transfers to
any literal finite host. The exact outside-state DMP mixture is retained. -/
theorem embedded_linear_event_bound_of_all_boundaries
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (θ : Parameters) (ξ : BoundaryCondition W) (E F : Set (Configuration G)) (c : ℝ)
    (h : ∀ η : BoundaryCondition V,
      c*(measure G θ η E).toReal ≤ (measure G θ η F).toReal) :
    c*(measure H θ ξ {C | embeddedConfigurationRestriction G H f hGH C ∈ E}).toReal ≤
      (measure H θ ξ {C | embeddedConfigurationRestriction G H f hGH C ∈ F}).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  let embeddedLinearInnerConfigs : Fintype (Configuration G) := Fintype.ofFinite _
  let embeddedLinearOutsideConfigs : Fintype (RemovedConfiguration H R) := Fintype.ofFinite _
  have hmix := law_embeddedConfigurationRestriction_eq_bind_frozenMarginal G H f hGH θ ξ
  have havg := pmf_bind_event_linear_bound (frozenMarginalLaw θ ξ R)
    (fun K => law G θ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))) E F c
    (fun K => h (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)))
  rw [← hmix] at havg
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top,
    PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at havg
  exact havg

end
end PottsContinuity.Push
