module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualResidualSourceUpper
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.DecreasingFKG

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration RSW
noncomputable section

/-- Native one-window estimates multiply on the SAME actual residual law. -/
theorem lemma4_native_primal_connectors_lower_of_nativeWindowBounds
    (n : ℕ) (q : Set.Ici (1:ℝ)) (record : Configuration (lemma4AmbientGraph n))
    (hwindow : ∀ j : Fin 3, 1/(1+(q:ℝ)^2) ≤
      (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
        (nativePrimalWindowNoncrossing (box (56*n)) (lemma4JointSourceReveal n record)
          ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)))).toReal) :
    (1/(1+(q:ℝ)^2))^3 ≤
      (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
        (lemma4NativePrimalConnectors n record)).toReal :=
  finiteLaw_three_lower_events_of_local_bounds _ _ _ _
    (fun j => nativePrimalWindowNoncrossing_isLowerSet _ _ _ _ _ _)
    _ (by positivity) hwindow

/-- Corrected actual-carrier chain. The upper half is record-free; the lower
half retains ONLY the honest native one-window numerical estimates. -/
theorem lemma4_actual_residual_chain_of_nativeWindowBounds
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ))
    (hwindow : ∀ record : Configuration (lemma4AmbientGraph n),
      record ∈ lemma4BandConstructionEvent n → ∀ j : Fin 3, 1/(1+(q:ℝ)^2) ≤
      (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
        (nativePrimalWindowNoncrossing (box (56*n)) (lemma4JointSourceReveal n record)
          ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)))).toReal) :
    (1/(1+(q:ℝ)^2))^3 * (measure (lemma4AmbientGraph n) (selfDualParameters q)
      (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4ActualResidualConnectorAnnulusEvent n)).toReal ∧
    (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
      (lemma4ActualResidualConnectorAnnulusEvent n)).toReal ≤ (annulusProbability (selfDualParameters q) 8 n)^2 := by
  constructor
  · apply lemma4_actual_residual_event_lower_of_native_connector_bounds n hn q
    intro record hr
    exact lemma4_native_primal_connectors_lower_of_nativeWindowBounds n q record (hwindow record hr)
  · exact lemma4_actual_residual_connector_annulus_probability_le_square _ n hn

/-- Exact band bound from the conditional lower chain, with the unchanged
constant. This name explicitly retains the unresolved native-window input. -/
theorem lemma4_band_to_square_bound_of_nativeWindowBounds
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ))
    (hwindow : ∀ record : Configuration (lemma4AmbientGraph n),
      record ∈ lemma4BandConstructionEvent n → ∀ j : Fin 3, 1/(1+(q:ℝ)^2) ≤
      (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
        (nativePrimalWindowNoncrossing (box (56*n)) (lemma4JointSourceReveal n record)
          ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)))).toReal) :
    (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
      (lemma4BandConstructionEvent n)).toReal ≤
        (1+(q:ℝ)^2)^3 * (annulusProbability (selfDualParameters q) 8 n)^2 := by
  have h := lemma4_actual_residual_chain_of_nativeWindowBounds n hn q hwindow
  have hp := h.1.trans h.2
  have heq (x : ℝ) : (1/(1+(q:ℝ)^2))^3*x=x/(1+(q:ℝ)^2)^3 := by
    rw [div_pow,one_pow,one_div,div_eq_mul_inv]
    exact mul_comm _ _
  rw [heq] at hp
  have hd : 0 < (1+(q:ℝ)^2)^3 := by positivity
  simpa only [mul_comm] using (div_le_iff₀ hd).mp hp

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
