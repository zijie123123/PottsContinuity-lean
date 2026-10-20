-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/Marginal.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredRemoval
public import PottsContinuity.FKC.FiniteFK.ProbabilityProduct

/-!
# The exact marginal after removing prewired edges

This proves the sampling equivalence on page 5 of the paper. Removed edges have
endpoints already identified by the boundary partition. The law of every other
edge is exactly the normalized FK weight with those edges omitted from sampling.
All original vertices and the original boundary partition are retained.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance marginalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance remainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance removedFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

/-- The normalized FK law when only the edges outside `R` are sampled. -/
def remainingLaw (q : ClusterWeight) (ξ : BoundaryCondition V) (R : Configuration G) :
    PMF (RemainingConfiguration G R) :=
  FiniteProbability.pmf (remainingWeight G q ξ R) (remainingWeight_pos G q ξ R)

/-- The Bernoulli weight on the removed edge carrier, normalized as a PMF. -/
def removedLaw (q : ClusterWeight) (R : Configuration G) :
    PMF (RemovedConfiguration G R) :=
  FiniteProbability.pmf (removedWeight G q R) (removedWeight_pos G q R)

/-- The partition function with the preselected edges removed from sampling. -/
def remainingPartitionFunction (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) : ℝ :=
  FiniteProbability.partition (remainingWeight G q ξ R)

theorem remainingPartitionFunction_pos (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) : 0 < remainingPartitionFunction G q ξ R :=
  FiniteProbability.partition_pos _ (remainingWeight_pos G q ξ R)

/-- The remaining law has precisely the reduced sampled-edge count of the finite FK law. -/
theorem remainingLaw_formula (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : RemainingConfiguration G R) :
    remainingLaw G q ξ R A = ENNReal.ofReal
      (edgeParameter q ^ A.val.card *
        (1 - edgeParameter q) ^ (Nat.card G.edgeSet - R.card - A.val.card) *
        q.val ^ componentCount G ξ A.val / remainingPartitionFunction G q ξ R) := rfl

variable [DecidableEq G.edgeSet]

/-- Summing over the removed Bernoulli states does not change the FK partition function. -/
theorem partitionFunction_eq_remaining (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v) :
    partitionFunction G q ξ = remainingPartitionFunction G q ξ R := by
  let e := configurationSplitEquiv G R
  have hw : weight G q ξ = fun C =>
      remainingWeight G q ξ R (e C).1 * removedWeight G q R (e C).2 := by
    funext C
    have hC : (e C).1.val ∪ (e C).2.val = C := e.symm_apply_apply C
    exact (congrArg (weight G q ξ) hC).symm.trans
      (weight_union_factorization G q ξ R hR (e C).1 (e C).2)
  unfold partitionFunction remainingPartitionFunction
  rw [hw, FiniteProbability.partition_equiv e
    (fun P => remainingWeight G q ξ R P.1 * removedWeight G q R P.2),
    FiniteProbability.partition_product, removedPartition_eq_one, mul_one]

/-- The complete joint law splits into the remaining FK law and the independent
Bernoulli law on edges whose endpoints are already boundary-identified. -/
theorem law_map_split (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v) :
    (law G q ξ).map (configurationSplitEquiv G R) =
      FiniteProbability.productPMF (remainingLaw G q ξ R) (removedLaw G q R) := by
  rw [law, remainingLaw, removedLaw, ← FiniteProbability.pmf_product]
  apply FiniteProbability.pmf_map_equiv_of_weight_eq
  intro C
  let P := configurationSplitEquiv G R C
  have hC : P.1.val ∪ P.2.val = C := (configurationSplitEquiv G R).symm_apply_apply C
  exact (congrArg (weight G q ξ) hC).symm.trans
    (weight_union_factorization G q ξ R hR P.1 P.2)

/-- Forgetting all prewired edges gives exactly the FK law on the remaining edges. -/
theorem law_map_remove (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v) :
    (law G q ξ).map (fun C => (configurationSplitEquiv G R C).1) =
      remainingLaw G q ξ R := by
  change (law G q ξ).map (Prod.fst ∘ configurationSplitEquiv G R) = _
  rw [← PMF.map_comp, law_map_split G q ξ R hR, FiniteProbability.productPMF_map_fst]

/-- If the removed edges are subsequently declared open for drawing, the two
sampling procedures still give the same distribution of drawing configurations. -/
theorem law_map_union_removed (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v) :
    (law G q ξ).map (fun C => C ∪ R) =
      (remainingLaw G q ξ R).map (fun A => A.val ∪ R) := by
  rw [← law_map_remove G q ξ R hR, PMF.map_comp]
  congr 1
  funext C
  exact Finset.sdiff_union_self_eq_union.symm

end

end PottsContinuity.FKC.FiniteFK
