module

public import PottsContinuity.Thm4.EndpointPassage
public import PottsContinuity.Thm4.FKCGraphBridge
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootPolynomialBound
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConnectionProbability

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section

/-- Actual connection to the top sheet is exponentially small also at q=4.
Finite-volume continuity extends the uniform strict-range separation estimate;
no convergence of infinite-volume laws in q is used. -/
theorem cover_connection_four_le_exp_positive (n : ℕ) (hn : 1 ≤ n)
    {u v : ParafermionicAmbientVertex n}
    (hu : u.val.2 = 0) (hv : v.val.2 = ((n ^ 5 : ℕ) : ℤ)) :
    (measure (ParafermionicAmbientGraph n) (selfDualParameters ⟨4, by norm_num⟩)
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
      {A | ActualConnected (ParafermionicAmbientGraph n) A u v}).toReal ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  apply fkc_event_upper_bound_at_four (ParafermionicAmbientGraph n)
    (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free
      (∅ : Set (ParafermionicAmbientVertex n)))
    {A | ActualConnected (ParafermionicAmbientGraph n) A u v}
  intro q
  have h := PottsContinuity.FKC.FiniteFK.parafermionicCoverConnection_probability_le_exp_positive
    n hn q (u := u) (v := v) hu hv
  change (PottsContinuity.FKC.FiniteFK.measure
    (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) q
    (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free
      (∅ : Set (ParafermionicAmbientVertex n)))
    {A | PottsContinuity.FKC.FiniteFK.ActualConnected
      (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) A u v}).toReal ≤ _ at h
  rw [← fkc_ambientGraph_eq n] at h
  exact h

/-- The corresponding actual bottom-sheet estimate at q=4. -/
theorem cover_connection_four_le_exp_negative (n : ℕ) (hn : 1 ≤ n)
    {u v : ParafermionicAmbientVertex n}
    (hu : u.val.2 = 0) (hv : v.val.2 = -((n ^ 5 : ℕ) : ℤ)) :
    (measure (ParafermionicAmbientGraph n) (selfDualParameters ⟨4, by norm_num⟩)
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
      {A | ActualConnected (ParafermionicAmbientGraph n) A u v}).toReal ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  apply fkc_event_upper_bound_at_four (ParafermionicAmbientGraph n)
    (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free
      (∅ : Set (ParafermionicAmbientVertex n)))
    {A | ActualConnected (ParafermionicAmbientGraph n) A u v}
  intro q
  have h := PottsContinuity.FKC.FiniteFK.parafermionicCoverConnection_probability_le_exp_negative
    n hn q (u := u) (v := v) hu hv
  change (PottsContinuity.FKC.FiniteFK.measure
    (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) q
    (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free
      (∅ : Set (ParafermionicAmbientVertex n)))
    {A | PottsContinuity.FKC.FiniteFK.ActualConnected
      (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) A u v}).toReal ≤ _ at h
  rw [← fkc_ambientGraph_eq n] at h
  exact h

end
end PottsContinuity.Thm4
