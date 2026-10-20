/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`ParafermionicPhaseAlgebra.lean`.
Adaptation: real q in the closed [1,4] subtype; include q = 4; omit SLE parameter.
Source: DCST 2015, TeX 1924-1936. Scalar algebra only.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

namespace PottsContinuity.Thm4

noncomputable section

/-- Loop fugacity, with real q rather than the strict q < 4 carrier. -/
def loopWeight (q : ℝ) : ℝ := Real.sqrt q

lemma loopWeight_sq (q : ℝ) (hq : 0 ≤ q) : loopWeight q ^ 2 = q :=
  Real.sq_sqrt hq

lemma loopWeight_pos (q : ℝ) (hq : 1 ≤ q) : 0 < loopWeight q :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hq)

lemma one_le_loopWeight (q : ℝ) (hq : 1 ≤ q) : 1 ≤ loopWeight q := by
  have hs := loopWeight_sq q (le_trans zero_le_one hq)
  have hp := loopWeight_pos q hq
  nlinarith only [hs, hp, hq]

lemma loopWeight_le_two (q : ℝ) (hq : q ≤ 4) : loopWeight q ≤ 2 := by
  dsimp [loopWeight]
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num; exact hq⟩

lemma loopWeight_lt_two (q : ℝ) (hq : q < 4) : loopWeight q < 2 := by
  dsimp [loopWeight]
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by norm_num; exact hq)

/-- The principal real spin branch used for q in the FK range. -/
def parafermionicSpin (q : Set.Icc (1 : ℝ) 4) : ℝ :=
  2 * Real.arcsin (loopWeight q.val / 2) / Real.pi

/-- The phase appearing in the local parafermionic turn identity. -/
def parafermionicPhase (q : Set.Icc (1 : ℝ) 4) : ℂ :=
  Complex.exp (Complex.I * (parafermionicSpin q * Real.pi / 2))

lemma arcsin_half_eq_pi_div_six : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma parafermionicSpin_mem (q : Set.Icc (1 : ℝ) 4) :
    1 / 3 ≤ parafermionicSpin q ∧ parafermionicSpin q ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhalf : 1 / 2 ≤ loopWeight q.val / 2 := by
    linarith [one_le_loopWeight q.val q.2.1]
  have hle : loopWeight q.val / 2 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 2)).2
    (loopWeight_le_two q q.2.2)
  have harcLower : Real.pi / 6 ≤ Real.arcsin (loopWeight q.val / 2) := by
    rw [← arcsin_half_eq_pi_div_six]
    exact Real.arcsin_le_arcsin hhalf
  have harcUpper : Real.arcsin (loopWeight q.val / 2) ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two _
  constructor
  · unfold parafermionicSpin
    apply (le_div_iff₀ hpi).2
    nlinarith
  · unfold parafermionicSpin
    apply (div_le_iff₀ hpi).2
    nlinarith

lemma parafermionicSpin_lt_one (q : Set.Icc (1 : ℝ) 4) (hq : (q : ℝ) < 4) :
    parafermionicSpin q < 1 := by
  have hangle : Real.arcsin (loopWeight q.val / 2) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr (by linarith only [loopWeight_lt_two q hq])
  unfold parafermionicSpin
  apply (div_lt_iff₀ Real.pi_pos).2
  linarith only [hangle]

@[simp] lemma parafermionicSpin_four : parafermionicSpin ⟨4, by norm_num⟩ = 1 := by
  norm_num [parafermionicSpin, loopWeight, Real.arcsin_one]
  field_simp

lemma parafermionicSpin_angle (q : Set.Icc (1 : ℝ) 4) :
    parafermionicSpin q * Real.pi / 2 = Real.arcsin (loopWeight q.val / 2) := by
  unfold parafermionicSpin
  field_simp [Real.pi_ne_zero]

lemma parafermionicPhase_ne_zero (q : Set.Icc (1 : ℝ) 4) : parafermionicPhase q ≠ 0 :=
  Complex.exp_ne_zero _

lemma parafermionicPhase_sub_inv (q : Set.Icc (1 : ℝ) 4) :
    parafermionicPhase q - (parafermionicPhase q)⁻¹ = Complex.I * loopWeight q.val := by
  let θ := Real.arcsin (loopWeight q.val / 2)
  have hθ : parafermionicSpin q * Real.pi / 2 = θ := parafermionicSpin_angle q
  have hz : parafermionicPhase q = Complex.exp (θ * Complex.I) := by
    simp [parafermionicPhase, ← hθ, mul_comm]
  have hneg : Complex.exp (-(θ * Complex.I)) = Real.cos (-θ) + Real.sin (-θ) * Complex.I := by
    simpa only [Complex.ofReal_neg, neg_mul] using Complex.exp_ofReal_mul_I (-θ)
  have hsin : Real.sin θ = loopWeight q.val / 2 := by
    dsimp [θ]
    exact Real.sin_arcsin (by linarith [loopWeight_pos q q.2.1]) (by linarith [loopWeight_le_two q q.2.2])
  rw [hz, ← Complex.exp_neg, Complex.exp_ofReal_mul_I, hneg,
    Real.cos_neg, Real.sin_neg, hsin]
  simp only [Complex.ofReal_neg]
  push_cast
  ring_nf

end
end PottsContinuity.Thm4
