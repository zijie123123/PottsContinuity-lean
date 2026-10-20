-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EdgeConditional.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Wiring
public import PottsContinuity.FKC.FiniteFK.Model

/-!
# The exact law of an edge within a wired component

Fix all edges except one original graph edge, whose endpoints are already in
the same wired component. The two remaining configurations have FK weight
odds `p / (1 - p) = sqrt q`. Their normalized probabilities therefore give open
conditional probability `p`. Boundary identification alone suffices for this
calculation, as required by the wired-edge convention on page 5 of the paper.

The conditional formula below is the ratio of actual singleton probabilities
on the two-element event `{A, insert e A}`. Its denominator is strictly positive.
It is not a claim that an arbitrary edge has open conditional probability `p`.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

/-- An absent edge inside an existing wired component changes only the two
Bernoulli factors in the FK weight. -/
theorem weight_insert_balance_of_related (q : ClusterWeight) (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    (1 - edgeParameter q) * weight G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * weight G q ξ A := by
  have hcard : A.card + 1 ≤ Nat.card G.edgeSet := by
    let : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
    rw [Nat.card_eq_fintype_card, ← Finset.card_insert_of_notMem he]
    exact Finset.card_le_univ _
  have hexponent : Nat.card G.edgeSet - A.card =
      (Nat.card G.edgeSet - (A.card + 1)) + 1 := by omega
  rw [weight, weight, Finset.card_insert_of_notMem he,
    componentCount_insert_eq_of_related ξ A huv hrelated, hexponent, pow_succ, pow_succ]
  ring

theorem weight_insert_eq_loopWeight_mul_of_related (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    weight G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      loopWeight q * weight G q ξ A := by
  have hparameter : (1 - edgeParameter q) * loopWeight q = edgeParameter q := by
    have h := (div_eq_iff (one_sub_edgeParameter_pos q).ne').mp (edgeParameter_odds q)
    exact (mul_comm _ _).trans h.symm
  apply mul_left_cancel₀ (one_sub_edgeParameter_pos q).ne'
  rw [weight_insert_balance_of_related q ξ A huv he hrelated, ← mul_assoc, hparameter]

/-- The exact open-to-closed weight odds are `sqrt q`. -/
theorem weight_insert_div_weight_of_related (q : ClusterWeight) (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    weight G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) / weight G q ξ A =
      loopWeight q := by
  apply (div_eq_iff (weight_pos G q ξ A).ne').mpr
  exact weight_insert_eq_loopWeight_mul_of_related q ξ A huv he hrelated

theorem configurationProbability_insert_balance_of_related (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    (1 - edgeParameter q) *
        configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * configurationProbability G q ξ A := by
  unfold configurationProbability
  rw [← mul_div_assoc, ← mul_div_assoc,
    weight_insert_balance_of_related q ξ A huv he hrelated]

/-- The open probability conditional on the two possible states of this edge,
with every other original edge fixed by `A`, equals the edge parameter. -/
theorem configurationProbability_pair_ratio_of_related (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) /
      (configurationProbability G q ξ A +
        configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A)) =
      edgeParameter q := by
  apply (div_eq_iff (add_pos (configurationProbability_pos G q ξ A)
    (configurationProbability_pos G q ξ _)).ne').mpr
  have h := configurationProbability_insert_balance_of_related q ξ A huv he hrelated
  nlinarith only [h]

end PottsContinuity.FKC.FiniteFK
