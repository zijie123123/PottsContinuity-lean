-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `ParafermionicBoundaryPhase.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.ParafermionicPhaseAlgebra

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

/-- The complementary spin used in the source boundary-phase coefficient. -/
def parafermionicBoundarySpin (q : ClusterWeight) : ℝ :=
  1 - parafermionicSpin q

lemma parafermionicBoundarySpin_bounds (q : ClusterWeight) :
    0 < parafermionicBoundarySpin q ∧
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
def parafermionicBoundaryPhase (q : ClusterWeight) : ℂ :=
  Complex.exp (Complex.I * (parafermionicBoundarySpin q * (2 * Real.pi)))

/-- The exact source Eq. 23 scalar coefficient `exp(i 2π σ̂) - 1`. -/
def parafermionicBoundaryCoefficient (q : ClusterWeight) : ℂ :=
  parafermionicBoundaryPhase q - 1

lemma parafermionicBoundaryCoefficient_norm (q : ClusterWeight) :
    ‖parafermionicBoundaryCoefficient q‖ =
      ‖2 * Real.sin (parafermionicBoundarySpin q * Real.pi)‖ := by
  unfold parafermionicBoundaryCoefficient parafermionicBoundaryPhase
  convert Complex.norm_exp_I_mul_ofReal_sub_one
      (parafermionicBoundarySpin q * (2 * Real.pi)) using 1 <;>
    push_cast <;> ring_nf

lemma parafermionicBoundaryCoefficient_norm_pos (q : ClusterWeight) :
    0 < ‖parafermionicBoundaryCoefficient q‖ := by
  rw [parafermionicBoundaryCoefficient_norm, Real.norm_eq_abs, abs_pos]
  have hb := parafermionicBoundarySpin_bounds q
  have hpi : 0 < Real.pi := Real.pi_pos
  have hangle : 0 < parafermionicBoundarySpin q * Real.pi ∧
      parafermionicBoundarySpin q * Real.pi < Real.pi := by
    constructor
    · exact mul_pos hb.1 hpi
    · nlinarith [hb.2.2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs.ne'

end
end PottsContinuity.FKC
