module

public import Mathlib.Tactic
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Finite spin and bond expansion

Finite products express the Potts weight as a sum over auxiliary bond states.
-/

@[expose] public section

namespace PottsContinuity.Thm1

noncomputable section

open Classical
open scoped BigOperators

variable {E S : Type*} [Fintype E]

/-- The factor assigned to one closed or open bond. -/
def esBondFactor (β : ℝ) (P : Prop) (b : Bool) : ℝ :=
  if b then (if P then 1 - Real.exp (-β) else 0) else Real.exp (-β)

/-- The unnormalized joint weight of a spin state and a bond state. -/
def esJointWeight (β : ℝ) (sat : S → E → Prop) (σ : S) (ω : E → Bool) : ℝ :=
  ∏ e, esBondFactor β (sat σ e) (ω e)

/-- The Gibbs weight for a given finite collection of agreement constraints. -/
def esGibbsWeight (β : ℝ) (sat : S → E → Prop) (σ : S) : ℝ :=
  Real.exp (β * ∑ e, if sat σ e then (1 : ℝ) else 0)

/-- The Bernoulli part of a bond weight. -/
def esBernoulliWeight (β : ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then 1 - Real.exp (-β) else Real.exp (-β)

theorem sum_esBondFactor (β : ℝ) (P : Prop) :
    ∑ b : Bool, esBondFactor β P b =
      Real.exp (-β) * Real.exp (β * if P then 1 else 0) := by
  by_cases h : P
  · simp only [Fintype.sum_bool, esBondFactor, Bool.false_eq_true, ↓reduceIte, h,
      mul_one]
    rw [← Real.exp_add]
    simp
  · simp [esBondFactor, h]

theorem sum_esJointWeight_bonds [Fintype S] (β : ℝ) (sat : S → E → Prop)
    (σ : S) :
    ∑ ω : E → Bool, esJointWeight β sat σ ω =
      Real.exp (-β) ^ Fintype.card E * esGibbsWeight β sat σ := by
  unfold esJointWeight
  rw [← Fintype.prod_sum]
  simp_rw [sum_esBondFactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.exp_sum, ← Finset.mul_sum]
  rfl

theorem esJointWeight_eq (β : ℝ) (sat : S → E → Prop)
    (σ : S) (ω : E → Bool) :
    esJointWeight β sat σ ω = esBernoulliWeight β ω *
      (if ∀ e, ω e = true → sat σ e then 1 else 0) := by
  have h (e : E) : esBondFactor β (sat σ e) (ω e) =
      (if ω e then 1 - Real.exp (-β) else Real.exp (-β)) *
        (if ω e = true → sat σ e then 1 else 0) := by
    cases ω e <;> by_cases hs : sat σ e <;> simp [esBondFactor, hs]
  simp only [esJointWeight, h, Finset.prod_mul_distrib,
    Fintype.prod_boole, esBernoulliWeight]

theorem esBernoulliWeight_eq (β : ℝ) (ω : E → Bool) :
    esBernoulliWeight β ω =
      (1 - Real.exp (-β)) ^ Nat.card {e // ω e = true} *
        Real.exp (-β) ^ Nat.card {e // ω e = false} := by
  simp only [esBernoulliWeight, Finset.prod_ite, Finset.prod_const,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Bool.not_eq_true]

variable [Fintype S]

/-- Summing over spins leaves the Bernoulli factor times the count of
assignments satisfying all open-bond constraints. -/
theorem sum_esJointWeight_spins (β : ℝ) (sat : S → E → Prop)
    (ω : E → Bool) :
    ∑ σ : S, esJointWeight β sat σ ω =
      esBernoulliWeight β ω * Nat.card {σ : S // ∀ e, ω e = true → sat σ e} := by
  simp only [esJointWeight_eq, ← Finset.mul_sum, Finset.sum_boole,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_esJointWeight_spins_pinned (β : ℝ) (sat : S → E → Prop)
    (ω : E → Bool) (pin : S → Prop) :
    (∑ σ : S, if pin σ then esJointWeight β sat σ ω else 0) =
      esBernoulliWeight β ω *
        Nat.card {σ : S // (∀ e, ω e = true → sat σ e) ∧ pin σ} := by
  classical
  have hpoint (σ : S) :
      (if pin σ then esJointWeight β sat σ ω else 0) =
        esBernoulliWeight β ω *
          (if (∀ e, ω e = true → sat σ e) ∧ pin σ then (1 : ℝ) else 0) := by
    rw [esJointWeight_eq]
    by_cases hp : pin σ <;> by_cases hc : ∀ e, ω e = true → sat σ e <;>
      simp [hp, hc]
  simp_rw [hpoint]
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The total unnormalized weight of the joint spin and bond system. -/
def esJointPartition (β : ℝ) (sat : S → E → Prop) : ℝ :=
  ∑ σ : S, ∑ ω : E → Bool, esJointWeight β sat σ ω

theorem esJointPartition_eq (β : ℝ) (sat : S → E → Prop) :
    esJointPartition β sat = Real.exp (-β) ^ Fintype.card E *
      ∑ σ : S, esGibbsWeight β sat σ := by
  simp only [esJointPartition, sum_esJointWeight_bonds, Finset.mul_sum]

theorem esJointPartition_pos [Nonempty S] (β : ℝ) (sat : S → E → Prop) :
    0 < esJointPartition β sat := by
  rw [esJointPartition_eq]
  apply mul_pos (pow_pos (Real.exp_pos _) _)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The normalized joint spin-bond mass. -/
def esJointProbability (β : ℝ) (sat : S → E → Prop)
    (σ : S) (ω : E → Bool) : ℝ :=
  esJointWeight β sat σ ω / esJointPartition β sat

theorem esJointProbability_nonneg [Nonempty S] {β : ℝ}
    (hβ : 0 ≤ β) (sat : S → E → Prop) (σ : S) (ω : E → Bool) :
    0 ≤ esJointProbability β sat σ ω := by
  apply div_nonneg _ (esJointPartition_pos β sat).le
  have hp : 0 ≤ 1 - Real.exp (-β) := by
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  apply Finset.prod_nonneg
  intro e _
  cases ω e
  · simp only [esBondFactor, Bool.false_eq_true, ↓reduceIte]
    positivity
  · simp only [esBondFactor, ↓reduceIte]
    split_ifs <;> simp [hp]

theorem sum_esJointProbability [Nonempty S] (β : ℝ) (sat : S → E → Prop) :
    ∑ σ : S, ∑ ω : E → Bool, esJointProbability β sat σ ω = 1 := by
  simp only [esJointProbability, ← Finset.sum_div]
  exact div_self (esJointPartition_pos β sat).ne'

/-- The spin marginal of the finite joint law is the Gibbs law for the
specified agreement constraints. -/
theorem esJointProbability_spin_marginal [Nonempty S]
    (β : ℝ) (sat : S → E → Prop) (σ : S) :
    ∑ ω : E → Bool, esJointProbability β sat σ ω =
      esGibbsWeight β sat σ / ∑ τ : S, esGibbsWeight β sat τ := by
  simp only [esJointProbability, ← Finset.sum_div,
    sum_esJointWeight_bonds, esJointPartition_eq]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_ne_zero _))

theorem sum_esJointProbability_spins_pinned [Nonempty S]
    (β : ℝ) (sat : S → E → Prop) (ω : E → Bool) (pin : S → Prop) :
    (∑ σ : S, if pin σ then esJointProbability β sat σ ω else 0) =
      esBernoulliWeight β ω *
        Nat.card {σ : S // (∀ e, ω e = true → sat σ e) ∧ pin σ} /
          esJointPartition β sat := by
  classical
  have hpoint (σ : S) :
      (if pin σ then esJointProbability β sat σ ω else 0) =
        (if pin σ then esJointWeight β sat σ ω else 0) /
          esJointPartition β sat := by
    rw [esJointProbability]
    by_cases hp : pin σ <;> simp [hp]
  calc
    _ = ∑ σ : S,
          ((if pin σ then esJointWeight β sat σ ω else 0) /
            esJointPartition β sat) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact hpoint σ
    _ = (∑ σ : S,
          if pin σ then esJointWeight β sat σ ω else 0) /
          esJointPartition β sat := by rw [Finset.sum_div]
    _ = (esBernoulliWeight β ω *
          Nat.card {σ : S // (∀ e, ω e = true → sat σ e) ∧ pin σ}) /
          esJointPartition β sat := by
      rw [sum_esJointWeight_spins_pinned]

end

end PottsContinuity.Thm1
