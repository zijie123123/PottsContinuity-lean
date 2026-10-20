module

public import PottsContinuity.Thm3.RSW.TiltedStripWindowReads
public import PottsContinuity.Thm3.Prop4.TiltedBoundaryLimits

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Thm3.Prop4 MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Literal closed-extension read of a finite sample on original strip edges. -/
def tiltedStripWindowOriginalRead (N : ℕ) (t : ℝ) (M : ℕ)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :
    TiltedConfiguration N t :=
  tiltedPlaneRestriction N t (tiltedWindowPlaneConfiguration N M t C)

/-- The source retained-bond dual window read of an actual finite sample. -/
def tiltedStripFiniteCentralDualRead (N : ℕ) (t : ℝ) (k M : ℕ)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :
    tiltedStripCentralRetainedBond N t k → Bool :=
  tiltedStripCentralDualConfiguration N t k (tiltedStripWindowOriginalRead N t M C)

/-- The reflected retained-bond window read of an actual finite sample. -/
def tiltedStripFiniteReflectedCentralDualRead (N : ℕ) (t : ℝ) (k M : ℕ)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :
    tiltedStripCentralRetainedBond N t k → Bool :=
  tiltedStripReflectedCentralDualConfiguration N t k (tiltedStripWindowOriginalRead N t M C)

end
end PottsContinuity.RSW
