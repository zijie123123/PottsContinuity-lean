module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import PottsContinuity.PD.FK.BoundaryComparison
public import PottsContinuity.PD.FK.ComponentSupermodular
public import PottsContinuity.PD.FK.FrozenBridge
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Finite-volume monotonicity in the edge parameter

For fixed cluster weight and boundary partition, the finite FK law is stochastically
increasing in `p`. The proof is Holley's criterion: the only new factor in the
cross-lattice condition comes from edges in `A \ B`, and is ordered by `p ≤ p'`.
The exact finite-volume bridge to the frozen `rcProb` is provided by
`PD.FK.configurationProbability_eq_rcProb`.
-/

@[expose] public section

namespace PottsContinuity.Critical

open scoped BigOperators

noncomputable section

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

local instance criticalMonotonicityEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- The Bernoulli product weight on a finite edge configuration. -/
def edgeMass (p : ℝ) (M : ℕ) (A : Configuration G) : ℝ :=
  p ^ A.card * (1 - p) ^ (M - A.card)

/-- Bernoulli product weights obey the cross-lattice inequality when their
parameters are ordered. -/
theorem edgeMass_cross_lattice_condition (p p' : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hp0 : 0 < p') (hp'0 : p' < 1)
    (hpp : p ≤ p') (A B : Configuration G) :
    edgeMass p (Nat.card G.edgeSet) A * edgeMass p' (Nat.card G.edgeSet) B ≤
      edgeMass p (Nat.card G.edgeSet) (A ∩ B) *
        edgeMass p' (Nat.card G.edgeSet) (A ∪ B) := by
  let M := Nat.card G.edgeSet
  let I := A ∩ B
  let U := A ∪ B
  let k := (A \ B).card
  let c := p ^ I.card * (1 - p) ^ (M - A.card) *
    p' ^ B.card * (1 - p') ^ (M - U.card)
  have hA : k + I.card = A.card := by
    dsimp [k, I]
    exact Finset.card_sdiff_add_card_inter A B
  have hU : k + B.card = U.card := by
    dsimp [k, U]
    exact Finset.card_sdiff_add_card A B
  have hM (C : Configuration G) : C.card ≤ M := by
    have hcard : Fintype.card G.edgeSet = M := by
      dsimp [M]
      exact (Nat.card_eq_fintype_card).symm
    exact (Finset.card_le_univ C).trans_eq hcard
  have hclosedA : M - I.card = (M - A.card) + k := by
    have hI := hM I
    have hAa := hM A
    omega
  have hclosedB : M - B.card = (M - U.card) + k := by
    have hBb := hM B
    have hUu := hM U
    omega
  have hpowA : p ^ A.card = p ^ I.card * p ^ k := by
    rw [← hA, pow_add, mul_comm]
  have hpowU : p' ^ U.card = p' ^ B.card * p' ^ k := by
    rw [← hU, pow_add, mul_comm]
  have hclosedApow : (1 - p) ^ (M - I.card) =
      (1 - p) ^ (M - A.card) * (1 - p) ^ k := by
    rw [hclosedA, pow_add]
  have hclosedBpow : (1 - p') ^ (M - B.card) =
      (1 - p') ^ (M - U.card) * (1 - p') ^ k := by
    rw [hclosedB, pow_add]
  have hL : edgeMass p M A * edgeMass p' M B =
      c * (p ^ k * (1 - p') ^ k) := by
    unfold edgeMass
    rw [hpowA, hclosedBpow]
    dsimp [c]
    ring
  have hR : edgeMass p M I * edgeMass p' M U =
      c * ((1 - p) ^ k * p' ^ k) := by
    unfold edgeMass
    rw [hclosedApow, hpowU]
    dsimp [c]
    ring
  have hbase : p * (1 - p') ≤ (1 - p) * p' := by
    nlinarith [hpp]
  have hpower : p ^ k * (1 - p') ^ k ≤ (1 - p) ^ k * p' ^ k := by
    have h := pow_le_pow_left₀
      (mul_nonneg hp.le (sub_nonneg.mpr hp'0.le)) hbase k
    rw [mul_pow, mul_pow] at h
    simpa [mul_comm] using h
  calc
    edgeMass p M A * edgeMass p' M B =
        c * (p ^ k * (1 - p') ^ k) := hL
    _ ≤ c * ((1 - p) ^ k * p' ^ k) :=
      mul_le_mul_of_nonneg_left hpower (by dsimp [c]; positivity)
    _ = edgeMass p M I * edgeMass p' M U := hR.symm

/-- The unnormalized random-cluster weights satisfy the cross-lattice condition
when the edge parameter increases and the cluster weight stays fixed. -/
theorem weight_parameter_cross_lattice_condition (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (ξ : BoundaryCondition V) (A B : Configuration G) :
    weight G θ ξ A * weight G θ' ξ B ≤
      weight G θ ξ (A ∩ B) * weight G θ' ξ (A ∪ B) := by
  have hedge := edgeMass_cross_lattice_condition
    (edgeParameter θ) (edgeParameter θ') (edgeParameter_pos θ)
    (edgeParameter_lt_one θ) (edgeParameter_pos θ') (edgeParameter_lt_one θ') hp A B
  have hcount := componentCount_supermodular ξ A B
  have hθnonneg : 0 ≤ θ.val := le_trans zero_le_one θ.property
  have hcluster : θ.val ^ componentCount G ξ A * θ.val ^ componentCount G ξ B ≤
      θ.val ^ componentCount G ξ (A ∩ B) * θ.val ^ componentCount G ξ (A ∪ B) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ θ.property hcount
  have hweightL : weight G θ ξ A * weight G θ' ξ B =
      (edgeMass (edgeParameter θ) (Nat.card G.edgeSet) A *
        edgeMass (edgeParameter θ') (Nat.card G.edgeSet) B) *
          (θ.val ^ componentCount G ξ A * θ.val ^ componentCount G ξ B) := by
    simp only [weight, edgeMass]
    rw [← hq]
    ring
  have hweightR : weight G θ ξ (A ∩ B) * weight G θ' ξ (A ∪ B) =
      (edgeMass (edgeParameter θ) (Nat.card G.edgeSet) (A ∩ B) *
        edgeMass (edgeParameter θ') (Nat.card G.edgeSet) (A ∪ B)) *
          (θ.val ^ componentCount G ξ (A ∩ B) *
            θ.val ^ componentCount G ξ (A ∪ B)) := by
    simp only [weight, edgeMass]
    rw [← hq]
    ring
  rw [hweightL, hweightR]
  calc
    (edgeMass (edgeParameter θ) (Nat.card G.edgeSet) A *
      edgeMass (edgeParameter θ') (Nat.card G.edgeSet) B) *
        (θ.val ^ componentCount G ξ A * θ.val ^ componentCount G ξ B)
        ≤ (edgeMass (edgeParameter θ) (Nat.card G.edgeSet) (A ∩ B) *
          edgeMass (edgeParameter θ') (Nat.card G.edgeSet) (A ∪ B)) *
            (θ.val ^ componentCount G ξ A * θ.val ^ componentCount G ξ B) :=
      mul_le_mul_of_nonneg_right hedge (mul_nonneg
        (pow_nonneg hθnonneg _) (pow_nonneg hθnonneg _))
    _ ≤ (edgeMass (edgeParameter θ) (Nat.card G.edgeSet) (A ∩ B) *
          edgeMass (edgeParameter θ') (Nat.card G.edgeSet) (A ∪ B)) *
            (θ.val ^ componentCount G ξ (A ∩ B) *
              θ.val ^ componentCount G ξ (A ∪ B)) :=
      mul_le_mul_of_nonneg_left hcluster (by
        unfold edgeMass
        exact mul_nonneg
          (mul_nonneg
            (pow_nonneg (edgeParameter_pos θ).le _)
            (pow_nonneg (one_sub_edgeParameter_pos θ).le _))
          (mul_nonneg
            (pow_nonneg (edgeParameter_pos θ').le _)
            (pow_nonneg (one_sub_edgeParameter_pos θ').le _)))

/-- The normalized finite FK probabilities satisfy Holley's cross-lattice
condition for two ordered edge parameters with the same cluster weight. -/
theorem configurationProbability_parameter_cross_lattice_condition (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (ξ : BoundaryCondition V) (A B : Configuration G) :
    configurationProbability G θ ξ A * configurationProbability G θ' ξ B ≤
      configurationProbability G θ ξ (A ∩ B) *
        configurationProbability G θ' ξ (A ∪ B) := by
  simp only [configurationProbability, div_mul_div_comm]
  apply (div_le_div_iff_of_pos_right
    (mul_pos (partitionFunction_pos G θ ξ) (partitionFunction_pos G θ' ξ))).2
  exact weight_parameter_cross_lattice_condition θ θ' hq hp ξ A B

/-- Finite-volume stochastic domination: every increasing observable has smaller
expectation at the lower edge parameter. This is on the ported finite FK model;
`PD.FK.configurationProbability_eq_rcProb` identifies each atom with the frozen
`rcProb` on the induced lattice graph. -/
theorem finite_fk_expectation_monotone (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (ξ : BoundaryCondition V) (f : Configuration G → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ A, f A * configurationProbability G θ ξ A) ≤
      ∑ A, f A * configurationProbability G θ' ξ A := by
  exact _root_.holley (μ := f) (f := configurationProbability G θ ξ)
    (g := configurationProbability G θ' ξ) hf0
    (fun A => (configurationProbability_pos G θ ξ A).le)
    (fun A => (configurationProbability_pos G θ' ξ A).le) hf
    (by rw [sum_configurationProbability, sum_configurationProbability])
    (configurationProbability_parameter_cross_lattice_condition θ θ' hq hp ξ)

end
end PottsContinuity.Critical
