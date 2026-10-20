module

public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.PD.Duality.FiniteDuality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

local instance freeDomainComparisonSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance freeDomainComparisonLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance freeDomainComparisonSmallConfigFintype : Fintype (Configuration G) :=
  @Finset.fintype G.edgeSet (PottsContinuity.PD.FK.edgeFintype G)
local instance freeDomainComparisonLargeConfigFintype : Fintype (Configuration H) :=
  @Finset.fintype H.edgeSet (PottsContinuity.PD.FK.edgeFintype H)

private theorem measure_toReal_eq_expectation_indicator
    [Fintype (Configuration G)]
    (q : Parameters) (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  refine Finset.sum_bij (fun A _ => A) ?_ ?_ ?_ ?_
  · intro A hA
    exact Finset.mem_univ _
  · intro A hA B hB hab
    exact hab
  · intro B hB
    exact ⟨B, by simp, rfl⟩
  · intro A hA
    simp [law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]

omit [Finite V] in
private theorem event_indicator_monotone
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    Monotone (S.indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ S
  · have hB := hS hAB hA
    simp [Set.indicator, hA, hB]
  · simp only [Set.indicator_of_notMem hA]
    have hnonneg : 0 ≤ S.indicator (fun _ => (1 : ℝ)) B := by
      by_cases hB : B ∈ S <;> simp [Set.indicator, hB]
    exact hnonneg

/-- A nonnegative increasing event on an embedded finite edge graph has no
larger probability in the smaller free model than its restriction pullback in
the containing free model. -/
theorem free_embedded_event_measure_le
    (f : V ↪ W) (hGH : G.map f ≤ H) (q : Parameters)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G q (BoundaryCondition.free ∅) S).toReal ≤
      (measure H q (BoundaryCondition.free ∅)
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  let F : Configuration G → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hF0 : ∀ A, 0 ≤ F A := by
    intro A
    by_cases hA : A ∈ S <;> simp [F, hA]
  have hF : Monotone F := event_indicator_monotone S hS
  have hcmp := embedded_free_expectation_le G H f hGH q ∅ ∅ F hF0 hF
  have hleft : (measure G q (BoundaryCondition.free ∅) S).toReal =
      expectation (law G q (BoundaryCondition.free ∅)) F := by
    simpa only [F] using measure_toReal_eq_expectation_indicator q
      (BoundaryCondition.free ∅) S
  have hright :
      (measure H q (BoundaryCondition.free ∅)
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal =
      expectation (law H q (BoundaryCondition.free ∅))
        (fun A => F (embeddedConfigurationRestriction G H f hGH A)) := by
    rw [measure_toReal_eq_expectation_indicator q
      (BoundaryCondition.free ∅)
      {A | embeddedConfigurationRestriction G H f hGH A ∈ S}]
    apply congrArg (expectation (law H q (BoundaryCondition.free ∅)))
    funext A
    by_cases hA : embeddedConfigurationRestriction G H f hGH A ∈ S <;>
      simp [F, Set.indicator, hA]
  exact hleft ▸ hcmp.trans_eq hright.symm

/-- The same comparison when the containing domain carries any boundary
partition above free. -/
theorem free_embedded_event_measure_le_of_target_partition
    (f : V ↪ W) (hGH : G.map f ≤ H) (q : Parameters)
    (η : BoundaryCondition W) (hη : (BoundaryCondition.free ∅).partition ≤ η.partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G q (BoundaryCondition.free ∅) S).toReal ≤
      (measure H q η
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  let T : Set (Configuration H) :=
    {A | embeddedConfigurationRestriction G H f hGH A ∈ S}
  have hT : IsUpperSet T := by
    intro A B hAB hA
    exact hS ((embeddedConfigurationRestriction_monotone G H f hGH) hAB) hA
  change (measure G q (BoundaryCondition.free ∅) S).toReal ≤
    (measure H q η T).toReal
  calc
    (measure G q (BoundaryCondition.free ∅) S).toReal ≤
        (measure H q (BoundaryCondition.free ∅) T).toReal :=
      free_embedded_event_measure_le f hGH q S hS
    _ ≤ (measure H q η T).toReal :=
      measure_boundary_comparison q (BoundaryCondition.free ∅) η hη T hT

theorem free_embedded_event_measure_le_at_selfDualParameter_of_target_partition
    (f : V ↪ W) (hGH : G.map f ≤ H) (q : Set.Ici (1 : ℝ))
    (η : BoundaryCondition W) (hη : (BoundaryCondition.free ∅).partition ≤ η.partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G (criticalParameters q) (BoundaryCondition.free ∅) S).toReal ≤
      (measure H (criticalParameters q) η
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  exact free_embedded_event_measure_le_of_target_partition f hGH
    (criticalParameters q) η hη S hS

end

end PottsContinuity.DualityExt
