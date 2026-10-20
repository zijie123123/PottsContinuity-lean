/- Scalar phase lemmas adapted from FKconvergence, an earlier formalization by the same author
that is not publicly accessible (see `related_formalizations` in formalization.yaml): files
`ParafermionicBoundaryPhase.lean` and `FiniteFK/ParafermionicModifiedPhaseAlgebra.lean`.
Adaptation: closed real [1,4] carrier; strict q<4 retained for nonzero coefficient;
new endpoint winding factor and correction of the source's scalar typo.
-/
module

public import PottsContinuity.Thm4.PhaseAlgebra

@[expose] public section

namespace PottsContinuity.Thm4

noncomputable section

/-- The complementary spin used in the source boundary-phase coefficient. -/
def parafermionicBoundarySpin (q : Set.Icc (1 : ℝ) 4) : ℝ :=
  1 - parafermionicSpin q

lemma parafermionicBoundarySpin_bounds (q : Set.Icc (1 : ℝ) 4) :
    0 ≤ parafermionicBoundarySpin q ∧
      parafermionicBoundarySpin q ≤ 2 / 3 ∧
      2 / 3 < 1 := by
  have h := parafermionicSpin_mem q
  unfold parafermionicBoundarySpin
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

/-- The unit phase in the source boundary coefficient. -/
def parafermionicBoundaryPhase (q : Set.Icc (1 : ℝ) 4) : ℂ :=
  Complex.exp (Complex.I * (parafermionicBoundarySpin q * (2 * Real.pi)))

/-- The exact source Eq. 23 scalar coefficient `exp(i 2π σ̂) - 1`. -/
def parafermionicBoundaryCoefficient (q : Set.Icc (1 : ℝ) 4) : ℂ :=
  parafermionicBoundaryPhase q - 1

lemma parafermionicBoundaryCoefficient_norm (q : Set.Icc (1 : ℝ) 4) :
    ‖parafermionicBoundaryCoefficient q‖ =
      ‖2 * Real.sin (parafermionicBoundarySpin q * Real.pi)‖ := by
  have hangle : parafermionicBoundarySpin q * (2 * Real.pi) / 2 =
      parafermionicBoundarySpin q * Real.pi := by ring
  simpa only [parafermionicBoundaryCoefficient, parafermionicBoundaryPhase,
    Complex.ofReal_mul, Complex.ofReal_ofNat, hangle] using
    Complex.norm_exp_I_mul_ofReal_sub_one (parafermionicBoundarySpin q * (2 * Real.pi))

lemma parafermionicBoundaryCoefficient_norm_pos (q : Set.Icc (1 : ℝ) 4)
    (hq : (q : ℝ) < 4) :
    0 < ‖parafermionicBoundaryCoefficient q‖ := by
  rw [parafermionicBoundaryCoefficient_norm, Real.norm_eq_abs, abs_pos]
  have hb := parafermionicBoundarySpin_bounds q
  have hpi : 0 < Real.pi := Real.pi_pos
  have hbpos : 0 < parafermionicBoundarySpin q := by
    dsimp [parafermionicBoundarySpin]
    linarith only [parafermionicSpin_lt_one q hq]
  have hangle : 0 < parafermionicBoundarySpin q * Real.pi ∧
      parafermionicBoundarySpin q * Real.pi < Real.pi := by
    constructor
    · exact mul_pos hbpos hpi
    · nlinarith [hb.2.2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs.ne'

/-- The actual modified quarter-turn phase used by the contour identity. -/
def parafermionicModifiedPhase (q : Set.Icc (1 : ℝ) 4) : ℂ :=
  Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)))

lemma parafermionicModifiedPhase_eq (q : Set.Icc (1 : ℝ) 4) :
    parafermionicModifiedPhase q = Complex.I * (parafermionicPhase q)⁻¹ := by
  have harg : Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)) =
      Complex.I * (Real.pi / 2) + -(Complex.I * (parafermionicSpin q * (Real.pi / 2))) := by
    simp [parafermionicBoundarySpin]
    ring
  have hquarter : Complex.exp (Complex.I * (Real.pi / 2)) = Complex.I := by
    rw [show Complex.I * (Real.pi / 2) = (Real.pi / 2) * Complex.I by ring,
      Complex.exp_mul_I]
    simp
  have hphase : parafermionicPhase q =
      Complex.exp (Complex.I * (parafermionicSpin q * (Real.pi / 2))) := by
    unfold parafermionicPhase
    congr 1
    ring
  rw [parafermionicModifiedPhase, harg, Complex.exp_add, hquarter, hphase,
    Complex.exp_neg]

lemma parafermionicModifiedPhase_ne_zero (q : Set.Icc (1 : ℝ) 4) :
    parafermionicModifiedPhase q ≠ 0 := by
  rw [parafermionicModifiedPhase_eq]
  exact mul_ne_zero Complex.I_ne_zero (inv_ne_zero (parafermionicPhase_ne_zero q))

lemma parafermionicModifiedPhase_add_inv (q : Set.Icc (1 : ℝ) 4) :
    parafermionicModifiedPhase q + (parafermionicModifiedPhase q)⁻¹ =
      (loopWeight q.val : ℂ) := by
  rw [parafermionicModifiedPhase_eq]
  have hz := parafermionicPhase_ne_zero q
  have h := parafermionicPhase_sub_inv q
  calc
    Complex.I * (parafermionicPhase q)⁻¹ + (Complex.I * (parafermionicPhase q)⁻¹)⁻¹ =
        Complex.I * (parafermionicPhase q)⁻¹ - Complex.I * parafermionicPhase q := by
          have hI : Complex.I⁻¹ = -Complex.I := by
            apply (mul_left_inj' Complex.I_ne_zero).mp
            simp [Complex.I_mul_I]
          rw [mul_inv_rev, hI, inv_inv]
          ring
    _ = (loopWeight q.val : ℂ) := by
      calc
        Complex.I * (parafermionicPhase q)⁻¹ - Complex.I * parafermionicPhase q =
            -Complex.I * (parafermionicPhase q - (parafermionicPhase q)⁻¹) := by ring
        _ = -Complex.I * (Complex.I * (loopWeight q.val : ℂ)) := by rw [h]
        _ = (loopWeight q.val : ℂ) := by
          calc
            -Complex.I * (Complex.I * (loopWeight q.val : ℂ)) =
                (-Complex.I * Complex.I) * (loopWeight q.val : ℂ) := by ring
            _ = (loopWeight q.val : ℂ) := by simp [Complex.I_mul_I]

lemma parafermionicModifiedPhase_quadratic (q : Set.Icc (1 : ℝ) 4) :
    parafermionicModifiedPhase q ^ 2 + 1 =
      (loopWeight q.val : ℂ) * parafermionicModifiedPhase q := by
  have hu := parafermionicModifiedPhase_ne_zero q
  have hsum := parafermionicModifiedPhase_add_inv q
  calc
    parafermionicModifiedPhase q ^ 2 + 1 =
        (parafermionicModifiedPhase q + (parafermionicModifiedPhase q)⁻¹) *
          parafermionicModifiedPhase q := by
            field_simp
    _ = (loopWeight q.val : ℂ) * parafermionicModifiedPhase q := by rw [hsum]

@[simp] lemma parafermionicBoundarySpin_four :
    parafermionicBoundarySpin ⟨4, by norm_num⟩ = 0 := by
  simp only [parafermionicBoundarySpin, parafermionicSpin_four, sub_self]

@[simp] lemma parafermionicBoundaryCoefficient_four :
    parafermionicBoundaryCoefficient ⟨4, by norm_num⟩ = 0 := by
  simp only [parafermionicBoundaryCoefficient, parafermionicBoundaryPhase,
    parafermionicBoundarySpin_four, zero_mul, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, sub_self]

/-- The deterministic winding factor of the modified observable (DCST TeX 1962-1968).
The endpoint uses winding itself. This factor is not an FK path expectation. -/
def modifiedWindingFactor (q : Set.Icc (1 : ℝ) 4) (w : ℝ) : ℂ :=
  if q.val = 4 then (w : ℂ)
  else Complex.exp (Complex.I * (parafermionicBoundarySpin q * w))

@[simp] lemma modifiedWindingFactor_four (w : ℝ) :
    modifiedWindingFactor ⟨4, by norm_num⟩ w = (w : ℂ) := by
  simp only [modifiedWindingFactor, ↓reduceIte]

end
end PottsContinuity.Thm4
