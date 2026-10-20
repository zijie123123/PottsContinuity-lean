-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicModifiedPhaseAlgebra.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.ParafermionicBoundaryPhase

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

/-- The actual modified quarter-turn phase used by the contour identity. -/
def parafermionicModifiedPhase (q : ClusterWeight) : ℂ :=
  Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)))

lemma parafermionicModifiedPhase_eq (q : ClusterWeight) :
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
    congr 1; ring
  rw [parafermionicModifiedPhase, harg, Complex.exp_add, hquarter, hphase,
    Complex.exp_neg]

lemma parafermionicModifiedPhase_ne_zero (q : ClusterWeight) :
    parafermionicModifiedPhase q ≠ 0 := by
  rw [parafermionicModifiedPhase_eq]
  exact mul_ne_zero Complex.I_ne_zero (inv_ne_zero (parafermionicPhase_ne_zero q))

lemma parafermionicModifiedPhase_add_inv (q : ClusterWeight) :
    parafermionicModifiedPhase q + (parafermionicModifiedPhase q)⁻¹ =
      (loopWeight q : ℂ) := by
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
    _ = (loopWeight q : ℂ) := by
      calc
        Complex.I * (parafermionicPhase q)⁻¹ - Complex.I * parafermionicPhase q =
            -Complex.I * (parafermionicPhase q - (parafermionicPhase q)⁻¹) := by ring
        _ = -Complex.I * (Complex.I * (loopWeight q : ℂ)) := by rw [h]
        _ = (loopWeight q : ℂ) := by
          calc
            -Complex.I * (Complex.I * (loopWeight q : ℂ)) =
                (-Complex.I * Complex.I) * (loopWeight q : ℂ) := by ring
            _ = (loopWeight q : ℂ) := by simp [Complex.I_mul_I]

lemma parafermionicModifiedPhase_quadratic (q : ClusterWeight) :
    parafermionicModifiedPhase q ^ 2 + 1 =
      (loopWeight q : ℂ) * parafermionicModifiedPhase q := by
  have hu := parafermionicModifiedPhase_ne_zero q
  have hsum := parafermionicModifiedPhase_add_inv q
  calc
    parafermionicModifiedPhase q ^ 2 + 1 =
        (parafermionicModifiedPhase q + (parafermionicModifiedPhase q)⁻¹) *
          parafermionicModifiedPhase q := by
            field_simp
    _ = (loopWeight q : ℂ) * parafermionicModifiedPhase q := by rw [hsum]

end
end PottsContinuity.FKC
