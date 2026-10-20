module

public import PottsContinuity.BD12.DRTAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! The homogeneous DRT law is exactly the existing finite FK law at
p = 1-exp(-beta), not an alternative notion of random-cluster measure. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK
open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtBridgeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

theorem drtWeight_homogeneous_eq (θ : Parameters) (ξ : BoundaryCondition V)
    (β : Set.Ioi (0 : ℝ))
    (hp : edgeParameter θ = 1 - Real.exp (-(β : ℝ))) (A : Configuration G) :
    drtWeight G ⟨θ.val, clusterWeight_pos θ⟩ ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β A =
      Real.exp (β : ℝ) ^ Nat.card G.edgeSet * weight G θ ξ A := by
  have hclosed : (1 - edgeParameter θ) * Real.exp (β : ℝ) = 1 := by
    rw [hp]
    simp only [sub_sub_cancel, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hopen : Real.exp (β : ℝ) - 1 = edgeParameter θ * Real.exp (β : ℝ) := by
    nlinarith [hclosed]
  have hc : A.card ≤ Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ A
  have hprod : (∏ e ∈ A, (Real.exp ((β : ℝ) * (1 : ℝ)) - 1)) =
      (Real.exp (β : ℝ) - 1) ^ A.card := by simp
  simp only [drtWeight, hprod, weight]
  rw [hopen, mul_pow]
  calc
    _ = (edgeParameter θ ^ A.card * θ.val ^ componentCount G ξ A) *
        Real.exp (β : ℝ) ^ A.card := by ring
    _ = (edgeParameter θ ^ A.card * θ.val ^ componentCount G ξ A) *
        (Real.exp (β : ℝ) ^ A.card *
          (((1 - edgeParameter θ) * Real.exp (β : ℝ)) ^
            (Nat.card G.edgeSet - A.card))) := by rw [hclosed, one_pow, mul_one]
    _ = _ := by
      have hpow : Real.exp (β : ℝ) ^ Nat.card G.edgeSet =
          Real.exp (β : ℝ) ^ A.card *
            Real.exp (β : ℝ) ^ (Nat.card G.edgeSet - A.card) := by
        rw [← pow_add, Nat.add_sub_of_le hc]
      rw [mul_pow, hpow]
      ring

theorem drtLaw_homogeneous_eq (θ : Parameters) (ξ : BoundaryCondition V)
    (β : Set.Ioi (0 : ℝ))
    (hp : edgeParameter θ = 1 - Real.exp (-(β : ℝ))) :
    drtLaw G ⟨θ.val, clusterWeight_pos θ⟩ ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β =
      law G θ ξ := by
  have hc : Real.exp (β : ℝ) ^ Nat.card G.edgeSet ≠ 0 :=
    (pow_pos (Real.exp_pos _) _).ne'
  have hz : partitionFunction G θ ξ ≠ 0 := (partitionFunction_pos G θ ξ).ne'
  ext A
  rw [drtLaw_apply, law_apply, drtWeight_homogeneous_eq G θ ξ β hp]
  simp only [configurationProbability, partitionFunction, FiniteProbability.partition]
  simp_rw [drtWeight_homogeneous_eq G θ ξ β hp]
  rw [← Finset.mul_sum]
  congr 1
  exact mul_div_mul_left _ _ hc

end
end PottsContinuity.BD12
