module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualNativePrimalLaw
public import PottsContinuity.Thm3.RSW.ResidualLawTransfer

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Push Exploration RSW MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The corrected source event uses the actual record-dependent residual,
with the exact original B_n selecting the successful source records. -/
def lemma4ActualResidualConnectorAnnulusEvent (n : ℕ) :
    Set (Configuration (lemma4AmbientGraph n)) :=
  {A | A ∈ lemma4BandConstructionEvent n ∧ A ∈ lemma4ActualResidualConnectors n A}

/-- The triple connector on the native original sample, without restoration. -/
def lemma4NativePrimalConnectors (n : ℕ) (record : Configuration (lemma4AmbientGraph n)) :
    Set (Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))) :=
  {C | ∀ j : Fin 3, C ∈ nativePrimalWindowNoncrossing (box (56*n))
    (lemma4JointSourceReveal n record) ((10*(j:ℤ)-13)*(n:ℤ))
      ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))}

/-- The sample-dependent carrier is constant on its actual stopping fibre. -/
theorem lemma4_actual_residual_event_on_record
    (n : ℕ) (hn : 1 ≤ n) (record A : Configuration (lemma4AmbientGraph n))
    (hrecord : record ∈ lemma4BandConstructionEvent n)
    (hA : A ∈ revealRecordEvent (lemma4JointSourceReveal n) record) :
    A ∈ lemma4ActualResidualConnectorAnnulusEvent n ↔
      nativeUnqueriedRead _ (lemma4JointSourceReveal n record) A ∈ lemma4NativePrimalConnectors n record := by
  have hband : A ∈ lemma4BandConstructionEvent n :=
    (lemma4BandConstructionEvent_readFrom_jointSourceReveal n hn record A hA).mpr hrecord
  change (A ∈ lemma4BandConstructionEvent n ∧ ∀ j : Fin 3,
    A ∈ residualPrimalWindowNoncrossing _ (lemma4JointSourceReveal n A) _ _ _ _) ↔
      ∀ j : Fin 3, nativeUnqueriedRead _ (lemma4JointSourceReveal n record) A ∈
        nativePrimalWindowNoncrossing _ _ _ _ _ _
  rw [hA.1]
  simp only [hband,true_and,nativePrimalWindowNoncrossing_unqueriedRead_iff]

/-- The native FK connector probability transfers to the corrected source
event on every successful actual record; no law/read premise is required. -/
theorem lemma4_actual_residual_record_probability_ge_native
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ))
    (record : Configuration (lemma4AmbientGraph n)) (hrecord : record ∈ lemma4BandConstructionEvent n) :
    (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
      (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
        (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
      (lemma4NativePrimalConnectors n record)).toReal ≤
    (((law (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (lemma4JointSourceReveal n) record) (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (lemma4JointSourceReveal_stable n) record]
        exact frozenStateEvent_support (selfDualParameters q) (BoundaryCondition.free ∅)
          _ (revealRecordConfiguration _ record))).toMeasure
            (lemma4ActualResidualConnectorAnnulusEvent n)).toReal := by
  apply residual_event_lower_of_residualLaw _ _ _ _ _ _ (lemma4_actual_record_native_primal_law n q record)
  intro A hs hA
  apply (lemma4_actual_residual_event_on_record n hn record A hrecord
    ((PMF.mem_support_filter_iff _).mp hs).1).mpr hA

/-- Only the numerical native connector estimate remains in this averaging
helper; all actual record, source-event and native-law identities are proved. -/
theorem lemma4_actual_residual_event_lower_of_native_connector_bounds
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Ici (1:ℝ)) (c : ℝ)
    (hlocal : ∀ record : Configuration (lemma4AmbientGraph n),
      record ∈ lemma4BandConstructionEvent n →
      c ≤ (measure (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n record))
        (selfDualParameters q) (frozenBoundary (BoundaryCondition.free ∅)
          (revealRecordConfiguration (lemma4JointSourceReveal n) record).val)
        (lemma4NativePrimalConnectors n record)).toReal) :
    c * (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
      (lemma4BandConstructionEvent n)).toReal ≤
    (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
      (lemma4ActualResidualConnectorAnnulusEvent n)).toReal := by
  rw [← lemma4SourceBandObservations_preimage n hn]
  apply stopped_event_lower_of_record_bounds _ _ _ (lemma4JointSourceReveal_stable n)
    (lemma4ActualResidualConnectorAnnulusEvent n) (lemma4SourceBandObservations n) c
  intro record hr
  have hrecord : record ∈ lemma4BandConstructionEvent n := by
    rw [← lemma4SourceBandObservations_preimage n hn]
    exact hr
  exact (hlocal record hrecord).trans (lemma4_actual_residual_record_probability_ge_native n hn q record hrecord)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
