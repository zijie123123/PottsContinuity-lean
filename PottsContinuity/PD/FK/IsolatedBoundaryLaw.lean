-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/IsolatedBoundaryLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/IsolatedBoundaryLaw.lean`.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q.
The weight identity uses the direct Bernoulli factors and component count formula. -/
module

public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import Mathlib.Tactic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PD.FK

noncomputable section

open PottsContinuity.PD.FK

variable {V W : Type*} [Finite V] [Finite W]

local instance isolatedBoundaryLawInnerEdgeFintype (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance isolatedBoundaryLawExtendedEdgeFintype (G : SimpleGraph V)
    (f : V ↪ W) : Fintype (G.map f).edgeSet := Fintype.ofFinite _

theorem weight_isolatedExtension_boundary_pullback (G : SimpleGraph V) (f : V ↪ W)
    (q : Parameters) (ξ : BoundaryCondition W) (A : Configuration G) :
    weight (G.map f) q ξ (isolatedExtensionConfigurationEquiv G f A) =
      weight G q (isolatedExtensionPullbackBoundary f ξ) A *
        q.val ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  rw [weight, weight, card_isolatedExtensionConfigurationEquiv, isolatedExtension_edge_card,
    componentCount_isolatedExtension_boundary_pullback G f ξ A, pow_add]
  simp only [mul_assoc]

theorem partitionFunction_isolatedExtension_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : Parameters) (ξ : BoundaryCondition W) :
    partitionFunction (G.map f) q ξ =
      partitionFunction G q (isolatedExtensionPullbackBoundary f ξ) *
        q.val ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  classical
  unfold partitionFunction FiniteProbability.partition
  rw [← (isolatedExtensionConfigurationEquiv G f).sum_comp]
  simp_rw [weight_isolatedExtension_boundary_pullback]
  rw [Finset.sum_mul]

theorem configurationProbability_isolatedExtension_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : Parameters) (ξ : BoundaryCondition W)
    (A : Configuration G) :
    configurationProbability (G.map f) q ξ (isolatedExtensionConfigurationEquiv G f A) =
      configurationProbability G q (isolatedExtensionPullbackBoundary f ξ) A := by
  rw [configurationProbability, configurationProbability,
    weight_isolatedExtension_boundary_pullback,
    partitionFunction_isolatedExtension_boundary_pullback]
  exact mul_div_mul_right _ _
    (pow_ne_zero _ (ne_of_gt (clusterWeight_pos q)))

theorem law_isolatedExtension_map_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : Parameters) (ξ : BoundaryCondition W) :
    (law G q (isolatedExtensionPullbackBoundary f ξ)).map
        (isolatedExtensionConfigurationEquiv G f) =
      law (G.map f) q ξ := by
  classical
  ext A
  obtain ⟨A, rfl⟩ := (isolatedExtensionConfigurationEquiv G f).surjective A
  rw [FiniteProbability.map_equiv_apply, Equiv.symm_apply_apply, law_apply, law_apply,
    configurationProbability_isolatedExtension_boundary_pullback]

end
end PottsContinuity.PD.FK
