module

public import PottsContinuity.Thm4.ExteriorConnectionCount
public import PottsContinuity.PD.FK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : Fintype (Configuration (ParafermionicAmbientGraph n)) :=
  Fintype.ofFinite _

/-- The expected number of connected exterior vertices is exactly the sum of
their actual connection probabilities under the free q=4 finite FK measure. -/
theorem connectedExteriorVertices_expected_card (n : ℕ) :
    (∑ A : Configuration (ParafermionicAmbientGraph n),
      coverFreeFourMass n A * ((connectedExteriorVertices n A).card : ℝ)) =
    ∑ v ∈ coverExteriorBoundary n,
      (measure (ParafermionicAmbientGraph n) (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        {A | ActualConnected (ParafermionicAmbientGraph n) A
          (parafermionicCoverBoxOrigin n) v}).toReal := by
  have hcard : ∀ A : Configuration (ParafermionicAmbientGraph n),
      ((connectedExteriorVertices n A).card : ℝ) =
      ∑ v ∈ coverExteriorBoundary n,
        if ActualConnected (ParafermionicAmbientGraph n) A (parafermionicCoverBoxOrigin n) v
        then (1 : ℝ) else 0 := by
    intro A
    simp [connectedExteriorVertices]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have h := measure_toReal_eq_indicator_sum
    (G := ParafermionicAmbientGraph n) (selfDualParameters ⟨4, by norm_num⟩)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
    {A | ActualConnected (ParafermionicAmbientGraph n) A (parafermionicCoverBoxOrigin n) v}
  symm
  apply h.trans
  apply Finset.sum_congr (by ext; simp)
  intro A _
  simp only [coverFreeFourMass, Set.indicator, Set.mem_ofPred_eq]

/-- The corrected q=4 boundary mass lower bound, at the explicit self-dual
parameter. Its source normalization is 2*pi and its constant is exactly 4/3.
The proof counts exterior strands rather than bounding individual windings. -/
theorem cover_boundary_connection_sum_lower_bound_four (n : ℕ) (hn : 1 ≤ n) :
    (4 / 3 : ℝ) ≤
    ∑ v ∈ coverExteriorBoundary n,
      (measure (ParafermionicAmbientGraph n) (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        {A | ActualConnected (ParafermionicAmbientGraph n) A
          (parafermionicCoverBoxOrigin n) v}).toReal := by
  have hbound :
      (∑ A : Configuration (ParafermionicAmbientGraph n),
        coverFreeFourMass n A * ((exteriorIncomingVisits n hn A).card : ℝ)) ≤
      3 * ∑ A : Configuration (ParafermionicAmbientGraph n),
        coverFreeFourMass n A * ((connectedExteriorVertices n A).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A _
    have hc : ((exteriorIncomingVisits n hn A).card : ℝ) ≤
        3 * ((connectedExteriorVertices n A).card : ℝ) := by
      exact_mod_cast exteriorIncomingVisits_card_le_three_connected n hn A
    have hp : 0 ≤ coverFreeFourMass n A :=
      (configurationProbability_pos _ _ _ A).le
    have h := mul_le_mul_of_nonneg_left hc hp
    nlinarith
  rw [exteriorIncomingVisits_expected_card_four, connectedExteriorVertices_expected_card] at hbound
  linarith

end
end PottsContinuity.Thm4
