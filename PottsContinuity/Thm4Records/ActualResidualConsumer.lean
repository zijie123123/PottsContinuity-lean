module

public import PottsContinuity.Thm4Records.NativePartition
public import PottsContinuity.Thm4Records.Selection
public import PottsContinuity.Thm4Plane.ScreenActiveConnectorDualConfig
public import PottsContinuity.FKC.FiniteFK.SlitScreenActualClosedGraph
public import PottsContinuity.PlanarMixed.Lemma4Connectors.SourceSlitRecordSurgery
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.Thm4Records.MaximalCompletion
public import PottsContinuity.Thm3.RSW.StoppedConnection
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane MeasureTheory PlanarMixed.Lemma4Connectors
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance actualConsumerEdgeEq (m : ℕ) : DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- Read only the literal unrevealed bonds, discarding isolated vertices. -/
def connectorRemainingRead (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X)) :
    Configuration (connectorIncidentGraph m hm X) :=
  incidentVertexConfigurationRead (connectorNativeGraph m hm X)
    ((edgeRestrictionConfigurationEquiv _ (connectorReveal m hm X)).symm U)

/-- The corrected connector event in decreasing primal form, on the residual
configuration alone. It tests no original queried bond. -/
def connectorRemainingNoncrossing (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Set (RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X)) :=
  connectorRemainingRead m hm X ⁻¹' (connectorNativeVertical m hm X)ᶜ

/-- The remaining law maps exactly to FK on the incident native carrier. -/
theorem connectorRemainingRead_law (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) (θ : Parameters)
    (ξ : BoundaryCondition (FKC.FiniteFK.SlitBoxVertex (16*m))) :
    (remainingLaw _ θ (frozenBoundary ξ (revealRecordConfiguration (connectorReveal m hm) X).val)
      (connectorReveal m hm X)).map (connectorRemainingRead m hm X) =
        law (connectorIncidentGraph m hm X) θ (connectorIncidentBoundary m hm X ξ) := by
  rw [← law_edgeRestriction_map,PMF.map_comp]
  have hfun : connectorRemainingRead m hm X ∘
      edgeRestrictionConfigurationEquiv (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X) =
      incidentVertexConfigurationRead (connectorNativeGraph m hm X) := by
    funext C
    simp only [Function.comp_apply,connectorRemainingRead,Equiv.symm_apply_apply]
  rw [hfun]
  exact connectorIncidentGraph_law m hm X θ ξ

/-- P-prime for the literal remaining configuration and induced boundary. -/
theorem connectorRemainingNoncrossing_lower_of_no_primal_connections
    (m : ℕ) (hm : 1 ≤ m) (q : Set.Ici (1:ℝ))
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hleft : X ∉ sidePrimalConnectionEvent m false)
    (hright : X ∉ sidePrimalConnectionEvent m true) :
    1/(1+(q:ℝ)^2) ≤
      ((remainingLaw _ (criticalParameters q)
        (frozenBoundary (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
          (revealRecordConfiguration (connectorReveal m hm) X).val)
        (connectorReveal m hm X)).toMeasure (connectorRemainingNoncrossing m hm X)).toReal := by
  have heval := congrArg (fun ρ : PMF (Configuration (connectorIncidentGraph m hm X)) =>
      ρ.toMeasure (connectorNativeVertical m hm X)ᶜ)
    (connectorRemainingRead_law m hm X (criticalParameters q)
      (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m))))
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at heval
  rw [show (connectorRemainingRead m hm X ⁻¹' (connectorNativeVertical m hm X)ᶜ) =
    connectorRemainingNoncrossing m hm X from rfl] at heval
  rw [heval]
  exact connectorIncidentNoncrossing_lower_of_no_primal_connections m hm q X hleft hright

/-- The remaining obligations are deterministic, uniform in q, and stated on
full source configurations. In particular this interface contains no FK law
or conditional-probability premise. -/
structure SlitConnectorResidualGeometry (m : ℕ) (hm : 1 ≤ m) : Prop where
  leftAlternative : SidePrimalDualAlternative m false
  rightAlternative : SidePrimalDualAlternative m true
  sourceSurgery : ∀ X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)),
    X ∈ connectorSourceEvent m →
    ∀ Y ∈ revealRecordEvent (connectorReveal m hm) X,
      (configurationSplitEquiv _ (connectorReveal m hm X) Y).1 ∈
        connectorRemainingNoncrossing m hm X → Y ∈ slitScreenConnectorEvent m

/-- The exact source factor follows from actual records once the two remaining
local geometric statements have been supplied. -/
theorem slitScreenConnectorFactor_of_residual_geometry
    (q : Set.Icc (1:ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (d : SlitConnectorResidualGeometry m hm) :
    (1/(1+(q:ℝ)^2)) * (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        FKC.FiniteFK.slitScreenRightCrossingEvent m)) ≤
      (slitScreenFiniteMeasure q m).real
        ((slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
          FKC.FiniteFK.slitScreenRightCrossingEvent m)) ∩ slitScreenConnectorEvent m) := by
  classical
  let qI : Set.Ici (1:ℝ) := ⟨q,q.2.1⟩
  let G := FKC.FiniteFK.slitBoxGraph (16*m)
  let ξ := Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m))
  let target := connectorSourceEvent m ∩ slitScreenConnectorEvent m
  have hT := connectorSelectedObservations_preimage_of_primalDualAlternatives m hm
    d.leftAlternative d.rightAlternative
  have hselected : ∀ X, stoppingObservationMap (connectorReveal m hm) X ∈
      connectorSelectedObservations m hm → X ∈ connectorSourceEvent m := by
    intro X hX
    rw [← hT]
    exact hX
  have hrecordTarget : ∀ X, stoppingObservationMap (connectorReveal m hm) X ∈
      connectorSelectedObservations m hm →
      1/(1+(qI:ℝ)^2) ≤
        (((law G (criticalParameters qI) ξ).filter
          (revealRecordEvent (connectorReveal m hm) X) (by
            rw [revealRecordEvent_eq_frozenStateEvent _ (connectorReveal_stable m hm) X]
            exact frozenStateEvent_support (criticalParameters qI) ξ _
              (revealRecordConfiguration (connectorReveal m hm) X))).toMeasure target).toReal := by
    intro X hX
    have hs := hselected X hX
    apply stopped_connection_lower_of_remaining_bound (criticalParameters qI) ξ
      (connectorReveal m hm) (connectorReveal_stable m hm) X
      (connectorRemainingNoncrossing m hm X) target (1/(1+(qI:ℝ)^2))
    · exact connectorRemainingNoncrossing_lower_of_no_primal_connections m hm qI X
        ((d.leftAlternative X).mp hs.2.1) ((d.rightAlternative X).mp hs.2.2)
    · intro Y hY hnon
      exact ⟨(connectorSourceEvent_readFrom_connectorReveal_of_primalDualAlternatives
        m hm d.leftAlternative d.rightAlternative X Y hY).mpr hs,
        d.sourceSurgery X hs Y hY hnon⟩
  have h := stopped_event_lower_of_record_bounds (criticalParameters qI) ξ
    (connectorReveal m hm) (connectorReveal_stable m hm) target
    (connectorSelectedObservations m hm) (1/(1+(qI:ℝ)^2)) hrecordTarget
  rw [hT] at h
  have hparam : criticalParameters qI = Thm4.selfDualParameters qI := rfl
  rw [hparam] at h
  simpa [slitScreenFiniteMeasure,qI,ξ,G,target,connectorSourceEvent,
    RSW.selfDualParameters,Measure.real_def] using h

end
end PottsContinuity.Thm4Records
