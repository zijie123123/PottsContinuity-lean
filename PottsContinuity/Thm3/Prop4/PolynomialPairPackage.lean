module

public import PottsContinuity.Thm3.Prop4.PolynomialDiagonalPenalty

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- A polynomial arm lower bound supplies the exact requested pair-field
shape, independently of the touching estimate or any decay premise. -/
theorem evenSquarePairKernel_package_of_polynomial_lower
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (d β : ℝ) (hd : 0 < d)
    (hpoly : ∀ n : ℕ, 1 ≤ n → d ≤ (n : ℝ)^β*RSW.oneArmProbability μ n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
        RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
          A*prop4PairKernel c ε (RSW.oneArmProbability μ) m := by
  refine ⟨1,zero_lt_one,?_⟩
  intro ε hε _
  obtain ⟨c,hc,hdiag⟩ := exists_diagonal_penalty_of_polynomial_lower (RSW.oneArmProbability μ)
    (RSW.oneArmProbability_pos (RSW.selfDualParameters q) μ hμ) d β hd hpoly ε hε
  refine ⟨1,c,zero_lt_one,hc,?_⟩
  intro m hm
  calc
    _ ≤ 1 := maxSquarePairProbability_le_one (RSW.selfDualParameters q) (2*m)
    _ ≤ Real.exp (c*(m : ℝ)^ε)*(RSW.oneArmProbability μ m)^2 := hdiag m hm
    _ ≤ prop4PairKernel c ε (RSW.oneArmProbability μ) m :=
      diagonal_le_prop4PairKernel (RSW.oneArmProbability μ) (fun _ => ENNReal.toReal_nonneg) ε c hc.le m
    _ = _ := (one_mul _).symm

end
end PottsContinuity.Thm3.Prop4
