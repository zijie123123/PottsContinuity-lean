/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/SubgraphIncreasingEventComparison.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open FiniteProbability
open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G H : SimpleGraph V}
local instance subgraphEventGraphFintype (K : SimpleGraph V) : Fintype K.edgeSet :=
  Fintype.ofFinite _
local instance subgraphEventGraphDecidableEq (K : SimpleGraph V) :
    DecidableEq K.edgeSet := Classical.decEq _

private theorem event_toReal_eq_expectation (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro A hA
  simp only [law_apply,
    ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]

omit [Finite V] in
private theorem event_indicator_nonneg (S : Set (Configuration G)) :
    ∀ A, 0 ≤ S.indicator (fun _ => (1 : ℝ)) A := by
  intro A
  by_cases h : A ∈ S <;> simp [Set.indicator, h]

omit [Finite V] in
private theorem event_indicator_mono (S : Set (Configuration G)) (hS : IsUpperSet S) :
    Monotone (S.indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ S
  · have hB : B ∈ S := hS hAB hA
    simp [Set.indicator, hA, hB]
  · simp only [Set.indicator_of_notMem hA]
    exact event_indicator_nonneg S B

/-- Increasing-event probability comparison under a same-vertex graph inclusion. -/
theorem subgraph_increasing_event_measure_toReal_le
    (hGH : G ≤ H) (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G q ξ S).toReal ≤
      (measure H q ξ {A | subgraphConfigurationRestriction hGH A ∈ S}).toReal := by
  classical
  let T : Set (Configuration H) := {A | subgraphConfigurationRestriction hGH A ∈ S}
  have hcmp := subgraph_expectation_le hGH q ξ
    (S.indicator (fun _ => (1 : ℝ))) (event_indicator_nonneg S)
    (event_indicator_mono S hS)
  have hpull :
      expectation (law H q ξ)
          (fun A => S.indicator (fun _ => (1 : ℝ))
            (subgraphConfigurationRestriction hGH A)) =
        expectation (law H q ξ) (T.indicator (fun _ => (1 : ℝ))) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro A hA
    rfl
  calc
    (measure G q ξ S).toReal =
        expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) :=
          event_toReal_eq_expectation q ξ S
    _ ≤ expectation (law H q ξ)
        (fun A => S.indicator (fun _ => (1 : ℝ))
          (subgraphConfigurationRestriction hGH A)) := hcmp
    _ = (measure H q ξ T).toReal := by
          rw [hpull, event_toReal_eq_expectation]

/-- The same comparison holds for any target event containing the pullback of the
smaller-graph event. -/
theorem subgraph_increasing_event_measure_toReal_le_of_pullback_subset
    (hGH : G ≤ H) (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) (hS : IsUpperSet S)
    (T : Set (Configuration H))
    (hST : ∀ A, subgraphConfigurationRestriction hGH A ∈ S → A ∈ T) :
    (measure G q ξ S).toReal ≤ (measure H q ξ T).toReal := by
  classical
  have hcmp := subgraph_expectation_le hGH q ξ
    (S.indicator (fun _ => (1 : ℝ))) (event_indicator_nonneg S)
    (event_indicator_mono S hS)
  have hpoint : ∀ A : Configuration H,
      S.indicator (fun _ => (1 : ℝ)) (subgraphConfigurationRestriction hGH A) ≤
        T.indicator (fun _ => (1 : ℝ)) A := by
    intro A
    by_cases hA : subgraphConfigurationRestriction hGH A ∈ S
    · have hT : A ∈ T := hST A hA
      simp [Set.indicator, hA, hT]
    · simp only [Set.indicator_of_notMem hA]
      by_cases hT : A ∈ T <;> simp [Set.indicator, hT]
  have hreal := hcmp.trans (expectation_mono (law H q ξ) _ _ hpoint)
  calc
    (measure G q ξ S).toReal =
        expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) :=
          event_toReal_eq_expectation q ξ S
    _ ≤ expectation (law H q ξ) (T.indicator (fun _ => (1 : ℝ))) := hreal
    _ = (measure H q ξ T).toReal := (event_toReal_eq_expectation q ξ T).symm

end
end PottsContinuity.PlanarMixed.Square
