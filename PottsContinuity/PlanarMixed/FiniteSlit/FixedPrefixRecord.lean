module

public import PottsContinuity.PlanarMixed.FixedOpenWalk
public import PottsContinuity.PlanarMixed.FiniteSlit.NativeSourceArms
public import PottsContinuity.PlanarMixed.FiniteSlit.RectanglePrefixCrosscuts
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip
public import PottsContinuity.PlanarMixed.FiniteSlit.ClippedReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRecordGeometry
public import PottsContinuity.PlanarMixed.RecordedArcBonds
public import PottsContinuity.BD12.CriticalValueConditional
public import PottsContinuity.BD12.CriticalValue
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.IntersectingSourceRecord
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK Exploration
noncomputable section
local instance fixedPrefixRecordEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Static lattice geometry of two retained source paths. The paths live in
the original full rectangle graph and do not depend on a sampled state. -/
def RetainedRectanglePathGeometry (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h)) : Prop :=
  1 ≤ x ∧ x ≤ (w:ℤ) ∧
  P.firstStart.val.2 = 0 ∧ P.secondStart.val.2 = 0 ∧
  P.firstEnd.val.1 = x-1 ∧ P.secondEnd.val.2 ≤ P.firstEnd.val.2 ∧
  P.secondEnd.val.1 = x ∧
  x ≤ P.firstStart.val.1 ∧ P.firstStart.val.1 < P.secondStart.val.1 ∧
  (∀ z ∈ P.second.support, x ≤ z.val.1) ∧
  (∀ z ∈ P.first.support, z ∉ P.second.support) ∧
  (∀ i < P.first.length, ¬ ((P.first.getVert i).val.1 = x-1 ∧
    P.secondEnd.val.2 ≤ (P.first.getVert i).val.2))

end
end PottsContinuity.PlanarMixed.FiniteSlit
