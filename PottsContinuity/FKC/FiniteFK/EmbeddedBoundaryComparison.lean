-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EmbeddedBoundaryComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.IsolatedBoundaryLaw
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability
open scoped BigOperators

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedBoundarySmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance embeddedBoundaryMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance embeddedBoundaryLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance embeddedBoundarySmallEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedBoundaryLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- Adding edges and exterior vertices cannot lower an increasing observable
when the inner law uses the exact boundary partition pulled back from the
outer graph. -/
theorem embedded_boundary_expectation_le
    (q : ClusterWeight) (ξ : BoundaryCondition W)
    (F : Configuration G → ℝ) (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) :
    expectation (law G q (isolatedExtensionPullbackBoundary f ξ)) F ≤
      expectation (law H q ξ)
        (fun A => F (embeddedConfigurationRestriction G H f hGH A)) := by
  have hsub := subgraph_expectation_le (G := G.map f) (H := H) hGH q ξ
    (fun A => F ((isolatedExtensionConfigurationEquiv G f).symm A))
    (fun A => hF0 _)
    (hF.comp (isolatedExtensionConfigurationOrderIso G f).symm.monotone)
  have hisoLaw : law G q (isolatedExtensionPullbackBoundary f ξ) =
      (law (G.map f) q ξ).map (Equiv.symm (isolatedExtensionConfigurationEquiv G f)) := by
    have h := congrArg
      (fun μ : PMF (Configuration (G.map f)) =>
        PMF.map (Equiv.symm (isolatedExtensionConfigurationEquiv G f)) μ)
      (law_isolatedExtension_map_boundary_pullback G f q ξ)
    simpa [PMF.map_comp, PMF.map_id] using h
  rw [hisoLaw, expectation_map]
  simpa [embeddedConfigurationRestriction] using hsub

private theorem embeddedBoundary_event_indicator_nonneg
    {α : Type*} (S : Set α) (x : α) :
    0 ≤ S.indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ S <;> simp [Set.indicator, h]

private theorem embeddedBoundary_event_indicator_mono
    {α : Type*} [Preorder α] (S : Set α) (hS : IsUpperSet S) :
    Monotone (S.indicator (fun _ => (1 : ℝ))) := by
  intro x y hxy
  by_cases hx : x ∈ S
  · have hy := hS hxy hx
    simp [Set.indicator, hx, hy]
  · simp only [Set.indicator_of_notMem hx]
    exact embeddedBoundary_event_indicator_nonneg S y

/-- Event-probability form of embedded comparison for arbitrary outer wiring.
The inner event is read from the actual original-edge restriction. -/
theorem embedded_boundary_probability_le
    (q : ClusterWeight) (ξ : BoundaryCondition W)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G q (isolatedExtensionPullbackBoundary f ξ) S).toReal ≤
      (measure H q ξ
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  let T : Set (Configuration H) :=
    {A | embeddedConfigurationRestriction G H f hGH A ∈ S}
  have hF := embedded_boundary_expectation_le G H f hGH q ξ
    (S.indicator (fun _ => (1 : ℝ)))
    (fun A => embeddedBoundary_event_indicator_nonneg S A)
    (embeddedBoundary_event_indicator_mono S hS)
  have hleft :
      (measure G q (isolatedExtensionPullbackBoundary f ξ) S).toReal =
        expectation (law G q (isolatedExtensionPullbackBoundary f ξ))
          (S.indicator (fun _ => (1 : ℝ))) := by
    rw [measure_toReal_eq_indicator_sum]
    unfold expectation
    apply Finset.sum_congr
    · ext A
      simp only [Finset.mem_univ]
    · intro A hA
      simp only [law_apply, ENNReal.toReal_ofReal
        (configurationProbability_pos G q (isolatedExtensionPullbackBoundary f ξ) A).le]
  have hright :
      (measure H q ξ T).toReal =
        expectation (law H q ξ) (T.indicator (fun _ => (1 : ℝ))) := by
    rw [measure_toReal_eq_indicator_sum]
    unfold expectation
    apply Finset.sum_congr
    · ext A
      simp only [Finset.mem_univ]
    · intro A hA
      simp only [law_apply, ENNReal.toReal_ofReal (configurationProbability_pos H q ξ A).le]
  have hpull :
      expectation (law H q ξ)
        (fun A => (S.indicator (fun _ => (1 : ℝ)))
          (embeddedConfigurationRestriction G H f hGH A)) =
      expectation (law H q ξ) (T.indicator (fun _ => (1 : ℝ))) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro A hA
    rfl
  calc
    (measure G q (isolatedExtensionPullbackBoundary f ξ) S).toReal =
        expectation (law G q (isolatedExtensionPullbackBoundary f ξ))
          (S.indicator (fun _ => (1 : ℝ))) := hleft
    _ ≤ expectation (law H q ξ)
          (fun A => (S.indicator (fun _ => (1 : ℝ)))
            (embeddedConfigurationRestriction G H f hGH A)) := hF
    _ = (measure H q ξ T).toReal := by rw [hpull, hright]

end
end PottsContinuity.FKC.FiniteFK
