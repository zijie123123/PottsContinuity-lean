-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SingleEdgeLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ComponentMerge
public import PottsContinuity.FKC.FiniteFK.EdgeConditional

/-!
# Exact one-edge FK conditional probabilities

With every other edge fixed, the open probability is p if the endpoints are
already connected after wiring and 1/(1+sqrt(q)) otherwise. These are ratios
of the actual positive singleton probabilities on the two-configuration event.
They are increasing with the other open edges, and obey uniform finite-energy
bounds. No association or multi-edge stochastic domination is asserted here.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

/-- The extra factor q records the single component lost upon opening. -/
theorem weight_insert_balance_of_not_related (q : ClusterWeight) (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    (1-edgeParameter q) * q.val * weight G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * weight G q ξ A := by
  have hc : A.card + 1 ≤ Nat.card G.edgeSet := by
    let : Fintype G.edgeSet := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← Finset.card_insert_of_notMem he]
    exact Finset.card_le_univ _
  have hec : Nat.card G.edgeSet - A.card = Nat.card G.edgeSet - (A.card+1) + 1 := by omega
  have hcomp := componentCount_insert_of_not_related ξ A huv hne
  rw [weight, weight, Finset.card_insert_of_notMem he, ← hcomp, hec,
    pow_succ, pow_succ, pow_succ]
  ring

/-- At the critical parameter the distinct-component weight odds are 1/sqrt(q). -/
theorem weight_insert_mul_loopWeight_of_not_related (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    weight G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) * loopWeight q =
      weight G q ξ A := by
  have h := weight_insert_balance_of_not_related q ξ A huv he hne
  rw [one_sub_edgeParameter, ← loopWeight_sq] at h
  change (1 / (1 + loopWeight q)) * loopWeight q ^ 2 * _ =
    (loopWeight q / (1 + loopWeight q)) * _ at h
  field_simp [(one_add_loopWeight_pos q).ne'] at h
  nlinarith [loopWeight_pos q]

/-- The exact open probability for two distinct endpoint components. -/
theorem configurationProbability_pair_ratio_of_not_related (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
      (configurationProbability G q ξ A +
        configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) =
      1 / (1 + loopWeight q) := by
  have h : configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) *
      loopWeight q = configurationProbability G q ξ A := by
    unfold configurationProbability
    rw [div_mul_eq_mul_div, weight_insert_mul_loopWeight_of_not_related q ξ A huv he hne]
  apply (div_eq_iff (add_pos (configurationProbability_pos G q ξ A)
    (configurationProbability_pos G q ξ _)).ne').mpr
  rw [one_div_mul_eq_div]
  apply (eq_div_iff (one_add_loopWeight_pos q).ne').mpr
  nlinarith only [h]

/-- The two possible conditional values are ordered for the full source range q>=1. -/
theorem lower_edge_conditional_le_parameter (q : ClusterWeight) :
    1 / (1 + loopWeight q) ≤ edgeParameter q := by
  change 1 / (1 + loopWeight q) ≤ loopWeight q / (1 + loopWeight q)
  exact (div_le_div_iff_of_pos_right (one_add_loopWeight_pos q)).mpr (one_le_loopWeight q)

/-- Uniform nontrivial lower and upper bounds on the actual two-state conditional. -/
theorem configurationProbability_pair_ratio_bounds (q : ClusterWeight)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A) :
    1 / (1 + loopWeight q) ≤
      configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
        (configurationProbability G q ξ A +
          configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) ∧
    configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
        (configurationProbability G q ξ A +
          configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) ≤
      edgeParameter q := by
  by_cases h : (componentSetoid G ξ A).r u v
  · rw [configurationProbability_pair_ratio_of_related q ξ A huv he h]
    exact ⟨lower_edge_conditional_le_parameter q, le_rfl⟩
  · rw [configurationProbability_pair_ratio_of_not_related q ξ A huv he h]
    exact ⟨le_rfl, lower_edge_conditional_le_parameter q⟩

end PottsContinuity.FKC.FiniteFK
