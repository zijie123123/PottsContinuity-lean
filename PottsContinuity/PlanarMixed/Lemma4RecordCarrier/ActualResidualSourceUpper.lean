module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualResidualTransport
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceBandClosedLoop
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualResidualRecordEvents
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.PlanarMixed.SourceGlobalWindows
public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import PottsContinuity.PlanarMixed.Lemma4Connectors.GlobalTraceLoop
public import PottsContinuity.PlanarTopology.OpenArchRayIndex
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import PottsContinuity.PlanarMixed.Square.RectangleVerticalReflection
public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import PottsContinuity.PlanarMixed.BandActiveComparisonGeometry
public import PottsContinuity.Thm3.RSW.StoppedRectangleDualRead
public import PottsContinuity.Thm3.RSW.FiniteDualClosure
public import PottsContinuity.PlanarMixed.Lemma4Connectors.TraceIndexScreen
public import PottsContinuity.PD.FK.IsolatedExtension
public import PottsContinuity.PlanarMixed.Lemma4Connectors.HullBoundaryCircuit
public import PottsContinuity.Exploration.BoundaryClusterDMP
public import PottsContinuity.PlanarMixed.Lemma4Connectors.SourceRecordedConnectors

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW MeasureTheory
noncomputable section

/-- Actual residual connectors give the full original loop geometry, with
no selected crossing record or comparison premise. -/
theorem lemma4_actual_residual_connectors_imply_core_geometry
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n)
    (hconnector : A ∈ lemma4ActualResidualConnectors n A) :
    A ∈ lemma4RecordedCoreGeometryEvent n := by
  obtain ⟨s,P,hclosed,hstrip,hcomponent⟩ := lemma4_source_band_exists_closed_core_loop n hn A hA
  refine ⟨s,P,hclosed,hstrip,?_,?_⟩
  · intro z hz u hu
    exact (hcomponent z hz u hu u (SimpleGraph.Reachable.refl _)).1
  · exact lemma4_actual_residual_connectors_imply_trace_noncrossings n hn A hA P hclosed hstrip hconnector

/-- Exact event transport to the already proved original-bond trace event. -/
theorem lemma4_actual_residual_connector_annulus_subset_trace
    (n : ℕ) (hn : 1 ≤ n) :
    lemma4ActualResidualConnectorAnnulusEvent n ⊆ lemma4TraceNoncrossingAnnulusEvent n := by
  intro A hA
  have hgeom := lemma4_actual_residual_connectors_imply_core_geometry n hn A hA.1 hA.2
  exact ⟨hA.1.1.2,hA.1.1.1,hgeom⟩

/-- Record-free eq.(16) for the ACTUAL residual connectors. It uses the proved
root-seed product bound and remains valid for overlapping outer boxes. -/
theorem lemma4_actual_residual_connector_annulus_probability_le_square
    (θ : Parameters) (n : ℕ) (hn : 1 ≤ n) :
    (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅)
      (lemma4ActualResidualConnectorAnnulusEvent n)).toReal ≤ (annulusProbability θ 8 n)^2 :=
  (measureReal_mono (lemma4_actual_residual_connector_annulus_subset_trace n hn)).trans
    (lemma4_trace_noncrossing_annulus_probability_le_square θ n)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
