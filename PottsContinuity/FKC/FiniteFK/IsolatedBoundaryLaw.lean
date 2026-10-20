-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/IsolatedBoundaryLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.IsolatedBoundaryComponents
public import PottsContinuity.FKC.FiniteFK.CriticalWeightNormalization
public import PottsContinuity.FKC.FiniteFK.ProbabilityProduct

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

open PottsContinuity.FKC

variable {V W : Type*} [Finite V] [Finite W]

local instance isolatedBoundaryLawInnerEdgeFintype (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance isolatedBoundaryLawExtendedEdgeFintype (G : SimpleGraph V)
    (f : V ↪ W) : Fintype (G.map f).edgeSet := Fintype.ofFinite _

theorem weight_isolatedExtension_boundary_pullback (G : SimpleGraph V) (f : V ↪ W)
    (q : ClusterWeight) (ξ : BoundaryCondition W) (A : Configuration G) :
    weight (G.map f) q ξ (isolatedExtensionConfigurationEquiv G f A) =
      weight G q (isolatedExtensionPullbackBoundary f ξ) A *
        q.val ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  rw [weight_eq_loopWeight_formula (G.map f) q ξ
      (isolatedExtensionConfigurationEquiv G f A),
    weight_eq_loopWeight_formula G q (isolatedExtensionPullbackBoundary f ξ) A,
    componentCount_isolatedExtension_boundary_pullback G f ξ A]
  rw [card_isolatedExtensionConfigurationEquiv, isolatedExtension_edge_card]
  have hexp : A.card + 2 *
      (componentCount G (isolatedExtensionPullbackBoundary f ξ) A +
        Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ)) =
      (A.card + 2 * componentCount G (isolatedExtensionPullbackBoundary f ξ) A) +
        2 * Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by omega
  rw [hexp, pow_add, pow_mul, loopWeight_sq]
  have hbase : 1 + loopWeight q ≠ 0 := (one_add_loopWeight_pos q).ne'
  field_simp [hbase]

theorem partitionFunction_isolatedExtension_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : ClusterWeight) (ξ : BoundaryCondition W) :
    partitionFunction (G.map f) q ξ =
      partitionFunction G q (isolatedExtensionPullbackBoundary f ξ) *
        q.val ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  classical
  unfold partitionFunction FiniteProbability.partition
  rw [← (isolatedExtensionConfigurationEquiv G f).sum_comp]
  simp_rw [weight_isolatedExtension_boundary_pullback]
  rw [Finset.sum_mul]

theorem configurationProbability_isolatedExtension_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : ClusterWeight) (ξ : BoundaryCondition W)
    (A : Configuration G) :
    configurationProbability (G.map f) q ξ (isolatedExtensionConfigurationEquiv G f A) =
      configurationProbability G q (isolatedExtensionPullbackBoundary f ξ) A := by
  rw [configurationProbability, configurationProbability,
    weight_isolatedExtension_boundary_pullback,
    partitionFunction_isolatedExtension_boundary_pullback]
  exact mul_div_mul_right _ _
    (pow_ne_zero _ (ne_of_gt (clusterWeight_pos q)))

theorem law_isolatedExtension_map_boundary_pullback
    (G : SimpleGraph V) (f : V ↪ W) (q : ClusterWeight) (ξ : BoundaryCondition W) :
    (law G q (isolatedExtensionPullbackBoundary f ξ)).map
        (isolatedExtensionConfigurationEquiv G f) =
      law (G.map f) q ξ := by
  classical
  exact FiniteProbability.pmf_map_equiv_of_common_factor
    (isolatedExtensionConfigurationEquiv G f)
    ((q.val ^ Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ))⁻¹)
    (weight G q (isolatedExtensionPullbackBoundary f ξ))
    (weight (G.map f) q ξ)
    (inv_pos.mpr (pow_pos (clusterWeight_pos q) _))
    (weight_pos G q (isolatedExtensionPullbackBoundary f ξ))
    (weight_pos (G.map f) q ξ)
    (fun A => by
      rw [weight_isolatedExtension_boundary_pullback]
      field_simp [pow_ne_zero _ (ne_of_gt (clusterWeight_pos q))])

end
end PottsContinuity.FKC.FiniteFK
