module

public import PottsContinuity.PlanarMixed.SourceGlobalWindows
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import PottsContinuity.PlanarMixed.Square.RectangleVerticalReflection
public import PottsContinuity.PlanarMixed.Lemma4Connectors.GlobalTraceLoop
public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import PottsContinuity.PlanarMixed.BandActiveComparisonGeometry
public import PottsContinuity.Thm3.RSW.StoppedRectangleDualRead
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.PlanarTopology.OpenArchRayIndex
public import PottsContinuity.Thm3.RSW.FiniteDualClosure
public import PottsContinuity.PlanarMixed.Lemma4Connectors.TraceIndexScreen

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite BD12 RSW Square MeasureTheory
noncomputable section

/-- Corrected source geometry without any annulus or probability premise. -/
def lemma4RecordedCoreGeometryEvent (n : ℕ) :
    Set (Configuration (PottsContinuity.squareLattice.induce (box (56*n) : Set LatticeVertex))) :=
  {A | ∃ s : LatticeVertex, ∃ P : PD.FK.squareLattice.Walk s s,
    finiteDualWalkClosed (box (56*n)) A P ∧
    (∀ z ∈ P.support, -3*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 3*(n:ℤ)-1) ∧
    (∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
      ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), rayIndex u.val P=1) ∧
    A ∈ lemma4PrimalNoncrossings (box (56*n)) (traceIndexRegion (box (56*n)) P) n}

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
