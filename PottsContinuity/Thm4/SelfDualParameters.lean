module

public import PottsContinuity.Thm4.PhaseAlgebra
public import PottsContinuity.PD.FK.SingleEdgeLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The explicit self-dual finite FK parameter

The parameter is the formula sqrt(q)/(1+sqrt(q)), with real q >= 1.
No identification with the genuine threshold is asserted.
The one-edge balances specialize PD/FK/{EdgeConditional,SingleEdgeLaw}.lean.
-/

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK

noncomputable section

/-- The actual finite-FK parameters at the explicit self-dual value. -/
def selfDualParameters (q : Set.Ici (1 : ℝ)) : Parameters where
  val := q.val
  property := q.property
  edgeProbability := ⟨loopWeight q / (1 + loopWeight q),
    div_pos (loopWeight_pos q q.property) (by linarith only [loopWeight_pos q q.property]),
    (div_lt_one (by linarith only [loopWeight_pos q q.property])).2 (by linarith)⟩

@[simp] lemma selfDualParameters_val (q : Set.Ici (1 : ℝ)) :
    (selfDualParameters q).val = q.val := rfl

lemma selfDualParameters_edgeParameter (q : Set.Ici (1 : ℝ)) :
    edgeParameter (selfDualParameters q) = Real.sqrt q / (1 + Real.sqrt q) := rfl

lemma selfDualParameters_one_sub_edgeParameter (q : Set.Ici (1 : ℝ)) :
    1 - edgeParameter (selfDualParameters q) = 1 / (1 + loopWeight q) := by
  change 1 - loopWeight q / (1 + loopWeight q) = _
  field_simp [(by linarith only [loopWeight_pos q q.property] : 1 + loopWeight q ≠ 0)]
  ring

lemma selfDualParameters_odds (q : Set.Ici (1 : ℝ)) :
    edgeParameter (selfDualParameters q) /
      (1 - edgeParameter (selfDualParameters q)) = loopWeight q := by
  rw [selfDualParameters_one_sub_edgeParameter]
  change (loopWeight q / (1 + loopWeight q)) / (1 / (1 + loopWeight q)) = _
  field_simp [(by linarith only [loopWeight_pos q q.property] : 1 + loopWeight q ≠ 0)]

@[simp] lemma selfDualParameters_four_edgeParameter :
    edgeParameter (selfDualParameters ⟨4, by norm_num⟩) = 2 / 3 := by
  rw [selfDualParameters_edgeParameter]
  norm_num

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

/-- Opening an absent edge whose endpoints are already related costs sqrt(q). -/
lemma weight_insert_eq_loopWeight_mul_of_related
    (q : Set.Ici (1 : ℝ)) (ξ : BoundaryCondition V) (A : Configuration G)
    {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    weight G (selfDualParameters q) ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      loopWeight q * weight G (selfDualParameters q) ξ A := by
  have h := weight_insert_balance_of_related (selfDualParameters q) ξ A huv he hrelated
  have hp := (one_sub_edgeParameter_pos (selfDualParameters q)).ne'
  apply (mul_left_cancel₀ hp)
  calc
    _ = edgeParameter (selfDualParameters q) * weight G (selfDualParameters q) ξ A := h
    _ = _ := by
      have hodds := (div_eq_iff hp).mp (selfDualParameters_odds q)
      calc
        _ = (loopWeight q * (1 - edgeParameter (selfDualParameters q))) *
            weight G (selfDualParameters q) ξ A :=
          congrArg (fun x => x * weight G (selfDualParameters q) ξ A) hodds
        _ = _ := by ring

/-- Opening an absent edge joining two wired components costs 1/sqrt(q). -/
lemma weight_insert_mul_loopWeight_of_not_related
    (q : Set.Ici (1 : ℝ)) (ξ : BoundaryCondition V) (A : Configuration G)
    {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    weight G (selfDualParameters q) ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) *
      loopWeight q = weight G (selfDualParameters q) ξ A := by
  have h := weight_insert_balance_of_not_related (selfDualParameters q) ξ A huv he hne
  have hp := one_sub_edgeParameter_pos (selfDualParameters q)
  have hs := loopWeight_pos q q.property
  have hq := loopWeight_sq q (le_trans zero_le_one q.property)
  have hodds := (div_eq_iff hp.ne').mp (selfDualParameters_odds q)
  have h' : (1 - edgeParameter (selfDualParameters q)) * loopWeight q ^ 2 *
      weight G (selfDualParameters q) ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
        edgeParameter (selfDualParameters q) * weight G (selfDualParameters q) ξ A := by
    simpa only [selfDualParameters_val, hq] using h
  apply (mul_left_cancel₀ (mul_ne_zero hp.ne' hs.ne'))
  calc
    _ = (1 - edgeParameter (selfDualParameters q)) * loopWeight q ^ 2 *
        weight G (selfDualParameters q) ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) := by ring
    _ = edgeParameter (selfDualParameters q) * weight G (selfDualParameters q) ξ A := h'
    _ = (loopWeight q * (1 - edgeParameter (selfDualParameters q))) *
        weight G (selfDualParameters q) ξ A :=
      congrArg (fun x => x * weight G (selfDualParameters q) ξ A) hodds
    _ = _ := by ring

end
end PottsContinuity.Thm4
