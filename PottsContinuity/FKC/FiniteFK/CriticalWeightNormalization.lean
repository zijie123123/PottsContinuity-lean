-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/CriticalWeightNormalization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Model
public import PottsContinuity.FKC.FiniteFK.Percolation
public import PottsContinuity.FKC.FiniteFK.ProbabilityProduct

@[expose] public section

open scoped BigOperators

namespace PottsContinuity.FKC.FiniteProbability

variable {α β : Type*} [Fintype α] [Fintype β]

lemma partition_mul_left (c : ℝ) (w : α → ℝ) :
    partition (fun a => c * w a) = c * partition w := by
  simp [partition, Finset.mul_sum]

variable [Nonempty α] [Nonempty β]

lemma pmf_map_equiv_of_common_factor (e : α ≃ β) (c : ℝ)
    (w : α → ℝ) (v : β → ℝ)
    (hc : 0 < c) (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 < v b)
    (h : ∀ a, w a = c * v (e a)) :
    (pmf w hw).map e = pmf v hv := by
  have hpart : partition w = c * partition v := by
    calc
      partition w = partition (fun a => c * v (e a)) := by
        congr 1
        funext a
        exact h a
      _ = c * partition (fun a => v (e a)) := partition_mul_left c _
      _ = c * partition v := by rw [partition_equiv e v]
  ext b
  rw [map_equiv_apply, pmf_apply, pmf_apply]
  rw [h (e.symm b), e.apply_symm_apply, hpart]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpv : partition v ≠ 0 := (partition_pos v hv).ne'
  congr 1
  field_simp [hcne, hpv]

end PottsContinuity.FKC.FiniteProbability

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance criticalWeightEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

open PottsContinuity.FKC

 theorem weight_eq_loopWeight_formula (q : ClusterWeight) (ξ : BoundaryCondition V)
    (A : Configuration G) :
    weight G q ξ A =
      loopWeight q ^ (A.card + 2 * componentCount G ξ A) /
        (1 + loopWeight q) ^ Nat.card G.edgeSet := by
  rw [weight, show edgeParameter q = loopWeight q / (1 + loopWeight q) by rfl]
  have hsub :
      1 - loopWeight q / (1 + loopWeight q) = 1 / (1 + loopWeight q) := by
    field_simp [(one_add_loopWeight_pos q).ne']
    ring
  rw [hsub, ← loopWeight_sq]
  change (loopWeight q / (1 + loopWeight q)) ^ A.card *
      (1 / (1 + loopWeight q)) ^ (Nat.card G.edgeSet - A.card) *
      (loopWeight q ^ 2) ^ componentCount G ξ A = _
  rw [div_pow, one_div_pow, ← pow_mul]
  have hcard := configuration_card_le_edge_card G A
  have hden :
      (1 + loopWeight q) ^ A.card *
        (1 + loopWeight q) ^ (Nat.card G.edgeSet - A.card) =
          (1 + loopWeight q) ^ Nat.card G.edgeSet := by
    rw [← pow_add]
    congr 1
    omega
  have hnum :
      loopWeight q ^ A.card *
        loopWeight q ^ (2 * componentCount G ξ A) =
          loopWeight q ^ (A.card + 2 * componentCount G ξ A) := by
    rw [← pow_add]
  have hbase : 1 + loopWeight q ≠ 0 := (one_add_loopWeight_pos q).ne'
  field_simp [hden, hnum, hbase]
  rw [← hden]
  ring

end

end PottsContinuity.FKC.FiniteFK

