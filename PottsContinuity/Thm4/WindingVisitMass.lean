module

public import PottsContinuity.Thm4.TotalWinding

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : Fintype (Configuration (ParafermionicAmbientGraph n)) :=
  Fintype.ofFinite _

/-- The genuine q=4 free FK mass at the explicit self-dual parameter. -/
def coverFreeFourMass (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) : ℝ :=
  configurationProbability (ParafermionicAmbientGraph n)
    (selfDualParameters ⟨4, by norm_num⟩)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A

/-- Real expectation of the actual suffix winding. -/
def pathWindingMean (n : ℕ) (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℝ :=
  ∑ A : Configuration (ParafermionicAmbientGraph n),
    coverFreeFourMass n A * parafermionicCoverPathWindingAtom n hn A (c, true)

/-- Incoming exterior ports actually visited by the exploration. -/
def exteriorIncomingVisits (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) : Finset (ParafermionicCoverFinitePort n) :=
  Finset.univ.filter fun c =>
    ¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
      parafermionicCoverIncomingPrimalLeft c.1 = true ∧
      (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support

theorem pathWindingMean_eq_re (n : ℕ) (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) :
    pathWindingMean n hn c =
      (parafermionicCoverModifiedPathExpectation ⟨4, by norm_num⟩ n hn (c, true)).re := by
  rw [modifiedPathExpectation_four_eq_winding_sum]
  simp [pathWindingMean, coverFreeFourMass]

/-- Interior expected winding cancels under the actual finite free FK law. -/
theorem internal_signed_winding_mean_zero (n : ℕ) (hn : 1 ≤ n) :
    (∑ c : ParafermionicCoverFinitePort n,
      if parafermionicCoverFinitePortOtherEndpointInBox n c then
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          pathWindingMean n hn c else 0) = 0 := by
  have h := congrArg Complex.re (modifiedPathExpectation_four_bulk_zero n hn)
  simp only [Finset.sum_filter] at h
  simp only [pathWindingMean_eq_re]
  simp only [Complex.re_sum, apply_ite Complex.re, Complex.zero_re,
    ite_mul, one_mul, neg_one_mul, Complex.neg_re] at h ⊢
  convert h using 1
  apply Finset.sum_congr (by ext; simp)
  intro c _
  rfl

/-- The full expected signed winding is exactly 2*pi. -/
theorem total_signed_winding_mean (n : ℕ) (hn : 1 ≤ n) :
    (∑ c : ParafermionicCoverFinitePort n,
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
        pathWindingMean n hn c) = 2 * Real.pi := by
  unfold pathWindingMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hp : ∀ A : Configuration (ParafermionicAmbientGraph n),
      (∑ c : ParafermionicCoverFinitePort n,
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          (coverFreeFourMass n A * parafermionicCoverPathWindingAtom n hn A (c, true))) =
      coverFreeFourMass n A * (2 * Real.pi) := by
    intro A
    rw [← total_signed_winding_sum n hn A, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simp_rw [hp]
  rw [← Finset.sum_mul]
  have hm : ∑ A : Configuration (ParafermionicAmbientGraph n), coverFreeFourMass n A = 1 :=
    by
      unfold coverFreeFourMass
      convert sum_configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) using 1
      apply Finset.sum_congr (by ext; simp)
      intro A _
      rfl
  rw [hm, one_mul]

/-- The exterior mean signed winding is exactly the positive source winding. -/
theorem exterior_signed_winding_mean (n : ℕ) (hn : 1 ≤ n) :
    (∑ c : ParafermionicCoverFinitePort n,
      if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          pathWindingMean n hn c else 0) = 2 * Real.pi := by
  have hi := internal_signed_winding_mean_zero n hn
  have ht := total_signed_winding_mean n hn
  have hsplit : (∑ c : ParafermionicCoverFinitePort n,
      (if parafermionicCoverFinitePortOtherEndpointInBox n c then
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          pathWindingMean n hn c else 0)) +
      (∑ c : ParafermionicCoverFinitePort n,
      if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          pathWindingMean n hn c else 0) =
      ∑ c : ParafermionicCoverFinitePort n,
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          pathWindingMean n hn c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : parafermionicCoverFinitePortOtherEndpointInBox n c <;> simp [hc]
  rw [hi, zero_add, ht] at hsplit
  exact hsplit

/-- The expected number of visited incoming exterior strands is exactly four.
The expectation is with respect to the complete actual q=4 finite free law. -/
theorem exteriorIncomingVisits_expected_card_four (n : ℕ) (hn : 1 ≤ n) :
    (∑ A : Configuration (ParafermionicAmbientGraph n),
      coverFreeFourMass n A * ((exteriorIncomingVisits n hn A).card : ℝ)) = 4 := by
  have h := exterior_signed_winding_mean n hn
  unfold pathWindingMean at h
  have hswap :
      (∑ c : ParafermionicCoverFinitePort n,
        if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
          (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
            (∑ A : Configuration (ParafermionicAmbientGraph n),
              coverFreeFourMass n A * parafermionicCoverPathWindingAtom n hn A (c, true))
        else 0) =
      ∑ A : Configuration (ParafermionicAmbientGraph n),
        ∑ c : ParafermionicCoverFinitePort n,
          if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
            (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
              (coverFreeFourMass n A * parafermionicCoverPathWindingAtom n hn A (c, true))
          else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : parafermionicCoverFinitePortOtherEndpointInBox n c <;>
      simp [hc, Finset.mul_sum]
  rw [hswap] at h
  have heq : ∀ A : Configuration (ParafermionicAmbientGraph n),
      (∑ c : ParafermionicCoverFinitePort n,
        if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
          (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
            (coverFreeFourMass n A * parafermionicCoverPathWindingAtom n hn A (c, true))
          else 0) =
      coverFreeFourMass n A * (Real.pi / 2) *
        ((exteriorIncomingVisits n hn A).card : ℝ) := by
    intro A
    have hp := exterior_signed_winding_sum n hn A
    have hc : ((exteriorIncomingVisits n hn A).card : ℝ) =
        ∑ c : ParafermionicCoverFinitePort n,
          if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
            parafermionicCoverIncomingPrimalLeft c.1 = true ∧
            (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
          then (1 : ℝ) else 0 := by
      simp [exteriorIncomingVisits]
    rw [hc, mul_assoc, ← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : parafermionicCoverFinitePortOtherEndpointInBox n c <;>
      simp [hc]
  simp_rw [heq] at h
  have hfactor : (∑ A : Configuration (ParafermionicAmbientGraph n),
      coverFreeFourMass n A * (Real.pi / 2) *
        ((exteriorIncomingVisits n hn A).card : ℝ)) =
      (Real.pi / 2) * ∑ A : Configuration (ParafermionicAmbientGraph n),
        coverFreeFourMass n A * ((exteriorIncomingVisits n hn A).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  rw [hfactor] at h
  nlinarith [Real.pi_pos]

end
end PottsContinuity.Thm4
