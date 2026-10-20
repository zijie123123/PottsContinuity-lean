module

public import PottsContinuity.PD.FK.EmbeddedMarginalLaw
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Thm4SideEuler

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedLowerInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance embeddedLowerOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance embeddedLowerMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance embeddedLowerInnerEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedLowerOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

private theorem innerMeasure_toReal_eq_expectation
    (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      FiniteProbability.expectation (law G q ξ)
        (S.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [measure_toReal_eq_indicator_sum]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
  · simp [Set.indicator, h]

private theorem outerMeasure_toReal_eq_expectation
    (q : Parameters) (ξ : BoundaryCondition W)
    (S : Set (Configuration H)) :
    (measure H q ξ S).toReal =
      FiniteProbability.expectation (law H q ξ)
        (S.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [measure_toReal_eq_indicator_sum]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos H q ξ A).le]
  · simp [Set.indicator, h]

/-- If every fixed exterior state induces boundary wiring at least as coarse
as the target partition, the target probability of an increasing event is
bounded by the marginal law of the host configuration restricted to the
embedded graph. -/
theorem embeddedConfigurationRestriction_preimage_measure_ge_of_frozen_partition
    (q : Parameters) (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (S : Set (Configuration G)) (hS : IsUpperSet S)
    (hpart : ∀ K : RemovedConfiguration H
        (subgraphRemovedEdges (G.map f) H),
      η.partition ≤
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition) :
    (measure G q η S).toReal ≤
      (measure H q ξ
        {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  classical
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let restr : Configuration H → Configuration G :=
    embeddedConfigurationRestriction G H f hGH
  let marg : PMF (RemovedConfiguration H R) := frozenMarginalLaw q ξ R
  let cond : RemovedConfiguration H R → PMF (Configuration G) := fun K =>
    law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
  let mix : PMF (Configuration G) := (law H q ξ).map restr
  let T : Set (Configuration H) := {A | restr A ∈ S}
  let ind : Configuration G → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hmix : mix = marg.bind cond := by
    simpa [mix, marg, cond, R, restr] using
      law_embeddedConfigurationRestriction_eq_bind_frozenMarginal
        G H f hGH q ξ
  have houter :
      (measure H q ξ T).toReal = FiniteProbability.expectation mix ind := by
    calc
      (measure H q ξ T).toReal =
          FiniteProbability.expectation (law H q ξ)
            (T.indicator (fun _ => (1 : ℝ))) :=
              outerMeasure_toReal_eq_expectation H q ξ T
      _ = FiniteProbability.expectation (law H q ξ)
          (fun A => ind (restr A)) := by
            apply congrArg (FiniteProbability.expectation (law H q ξ))
            funext A
            by_cases h : restr A ∈ S <;>
              simp [T, ind, Set.indicator, h]
      _ = FiniteProbability.expectation mix ind := by
            simpa [mix, ind] using
              (FiniteProbability.expectation_map (law H q ξ) restr ind).symm
  have hconditional : ∀ K : RemovedConfiguration H R,
      FiniteProbability.expectation (law G q η) ind ≤
        FiniteProbability.expectation (cond K) ind := by
    intro K
    have hbound := measure_boundary_comparison q η
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
      (hpart K) S hS
    rw [innerMeasure_toReal_eq_expectation G q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S,
      innerMeasure_toReal_eq_expectation G q η S] at hbound
    simpa [cond, ind] using hbound
  have havg := FiniteProbability.le_expectation_bind marg cond ind
    (FiniteProbability.expectation (law G q η) ind) hconditional
  have hinner :
      FiniteProbability.expectation (law G q η) ind =
        (measure G q η S).toReal := by
    simpa [ind] using (innerMeasure_toReal_eq_expectation G q η S).symm
  have hresult :
      (measure G q η S).toReal ≤ (measure H q ξ T).toReal := by
    calc
      (measure G q η S).toReal =
          FiniteProbability.expectation (law G q η) ind := hinner.symm
      _ ≤ FiniteProbability.expectation (marg.bind cond) ind := by
        simpa only [FiniteProbability.expectation_bind] using havg
      _ = FiniteProbability.expectation mix ind := by
        exact congrArg (fun μ => FiniteProbability.expectation μ ind) hmix.symm
      _ = (measure H q ξ T).toReal := houter.symm
  simpa [T] using hresult

end
end PottsContinuity.Thm4SideEuler
