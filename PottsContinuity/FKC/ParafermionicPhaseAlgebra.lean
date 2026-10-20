-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `ParafermionicPhaseAlgebra.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Parameters
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

/-- The principal real spin branch used for q in the FK range. -/
def parafermionicSpin (q : ClusterWeight) : ℝ :=
  2 * Real.arcsin (loopWeight q / 2) / Real.pi

/-- The phase appearing in the local parafermionic turn identity. -/
def parafermionicPhase (q : ClusterWeight) : ℂ :=
  Complex.exp (Complex.I * (parafermionicSpin q * Real.pi / 2))

lemma arcsin_half_eq_pi_div_six : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma parafermionicSpin_mem (q : ClusterWeight) :
    1 / 3 ≤ parafermionicSpin q ∧ parafermionicSpin q < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhalf : 1 / 2 ≤ loopWeight q / 2 := by
    linarith [one_le_loopWeight q]
  have hlt : loopWeight q / 2 < 1 := (div_lt_one (by norm_num : (0 : ℝ) < 2)).2
    (loopWeight_lt_two q)
  have harcLower : Real.pi / 6 ≤ Real.arcsin (loopWeight q / 2) := by
    rw [← arcsin_half_eq_pi_div_six]
    exact Real.arcsin_le_arcsin hhalf
  have harcUpper : Real.arcsin (loopWeight q / 2) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr hlt
  constructor
  · unfold parafermionicSpin
    apply (le_div_iff₀ hpi).2
    nlinarith
  · unfold parafermionicSpin
    apply (div_lt_iff₀ hpi).2
    nlinarith

lemma parafermionicSpin_angle (q : ClusterWeight) :
    parafermionicSpin q * Real.pi / 2 = Real.arcsin (loopWeight q / 2) := by
  unfold parafermionicSpin
  field_simp [Real.pi_ne_zero]

lemma parafermionicPhase_ne_zero (q : ClusterWeight) : parafermionicPhase q ≠ 0 :=
  Complex.exp_ne_zero _

lemma parafermionicPhase_sub_inv (q : ClusterWeight) :
    parafermionicPhase q - (parafermionicPhase q)⁻¹ = Complex.I * loopWeight q := by
  let θ := Real.arcsin (loopWeight q / 2)
  have hθ : parafermionicSpin q * Real.pi / 2 = θ := parafermionicSpin_angle q
  have hz : parafermionicPhase q = Complex.exp (θ * Complex.I) := by
    simp [parafermionicPhase, ← hθ, mul_comm]
  have hneg : Complex.exp (-(θ * Complex.I)) = Real.cos (-θ) + Real.sin (-θ) * Complex.I := by
    convert Complex.exp_ofReal_mul_I (-θ) using 1
    simp only [Complex.ofReal_neg]
    ring_nf
  have hsin : Real.sin θ = loopWeight q / 2 := by
    dsimp [θ]
    exact Real.sin_arcsin (by linarith [loopWeight_pos q]) (by linarith [loopWeight_lt_two q])
  rw [hz, ← Complex.exp_neg, Complex.exp_ofReal_mul_I, hneg,
    Real.cos_neg, Real.sin_neg, hsin]
  simp only [Complex.ofReal_neg]
  push_cast
  ring_nf

end
end PottsContinuity.FKC
