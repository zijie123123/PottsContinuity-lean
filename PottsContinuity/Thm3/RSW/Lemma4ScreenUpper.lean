module

public import PottsContinuity.Thm3.RSW.OverlappingAnnulusScreens
public import PottsContinuity.Thm3.RSW.Lemma4UpperConditional

/-! # The actual Lemma-4 screened-pair upper bound at the source centers -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- At centers (±5n,0), the genuine two-annulus/two-screen event has probability
at most a_n². The radius-8n reference boxes overlap. No selected random domain,
complete-record hypothesis or conditional probability estimate is an input. -/
theorem lemma4_screened_annulus_pair_probability_le_square (θ : Parameters) (n : ℕ) :
    (measure (squareLattice.induce (box (56*n) : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      (screenedAnnulusPairEvent (box (56*n))
        (latticeBox (-5*(n:ℤ),0) (8*n)) (latticeBox (5*(n:ℤ),0) (8*n))
        (-5*(n:ℤ),0) (5*(n:ℤ),0) n n)).toReal ≤ (annulusProbability θ 8 n)^2 := by
  have hU₁ := lemma4_reference_subset_ambient n (-5*(n:ℤ),0) (by
    constructor
    · change |(-5:ℤ)*(n:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_of_nonpos (by omega)]
      omega
    · change |(0:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_zero]
      omega)
  have hU₂ := lemma4_reference_subset_ambient n (5*(n:ℤ),0) (by
    constructor
    · change |(5:ℤ)*(n:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_of_nonneg (by omega)]
    · change |(0:ℤ)| ≤ 5*(n:ℤ)
      rw [abs_zero]
      omega)
  have hleft : ∀ v ∈ latticeBox (-5*(n:ℤ),0) (8*n), v.1 ≤ (5*(n:ℤ),0).1 := by
    intro v hv
    rw [mem_latticeBox] at hv
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hv
    change v.1 ≤ 5*(n:ℤ)
    omega
  have h := screenedAnnulusPair_probability_le_local_product_of_rightSeparation
    (box (56*n)) (latticeBox (-5*(n:ℤ),0) (8*n)) (latticeBox (5*(n:ℤ),0) (8*n))
    hU₁ hU₂ θ (-5*(n:ℤ),0) (5*(n:ℤ),0) n n hleft
  rw [translated_box_annulus_probability_eq,translated_box_annulus_probability_eq] at h
  rw [pow_two]
  exact h

end
end PottsContinuity.RSW
