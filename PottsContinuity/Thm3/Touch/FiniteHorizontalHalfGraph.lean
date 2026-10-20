module

public import PottsContinuity.Thm3.Touch.FiniteSplitDomains
public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PlanarTopology.RectanglePolygonDomain
public import PottsContinuity.PlanarTopology.RectangleGraphBridge
public import PottsContinuity.PlanarTopology.RotatedPolygon
public import Schoenflies.GeneralCrosscut
public import Schoenflies.FaceCyclesProof
public import PottsContinuity.PlanarTopology.OccurrenceDualHalfSegments
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Topology.Connected.LocallyConnected
public import Schoenflies.AccessibleJoin
public import Schoenflies.JordanClosed
public import PottsContinuity.PlanarTopology.PolygonFourArcExistence
public import PottsContinuity.PlanarTopology.DobrushinDualProjection
public import PottsContinuity.PlanarTopology.DobrushinExteriorExtraction

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.Thm3.Prop4
open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.PlanarTopology

/-!
# The level-zero split as a rectangle graph
-/

/-- The rectangular Jordan polygon for the left half of the horizontal strip,
cyclically started at the central top corner. -/
def horizontalLeftSplitPolygon (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    LatticePolygon (2*L+2*(2*n)-3) :=
  rotateLatticePolygon
    (rectangleLatticePolygon (-(L : ℤ),0) L (2*n) (by omega) (by omega))
    ((L+2*n : ℕ) : ZMod ((2*L+2*(2*n)-3)+3))

/-- The rectangle graph is identified with the closure graph of the chosen
polygon presentation. -/
theorem horizontalLeftSplitPolygon_domain_eq (n L : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (δ : FKC.PositiveMesh) :
    (rectangleLatticePolygon (-(L : ℤ), 0) L (2*n) (by omega) (by omega)).domain δ =
      (horizontalLeftSplitPolygon n L hn hL).domain δ := by
  unfold horizontalLeftSplitPolygon
  exact (rotateLatticePolygon_domain _ _ _).symm

end PottsContinuity.Thm3.Touch
