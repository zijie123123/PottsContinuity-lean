module

public import PottsContinuity.Thm3.Touch.FiniteHorizontalDualCarrierEmbedding
public import PottsContinuity.Thm3.Touch.FiniteSplitDomains
public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.DualityExt.PositiveInducedSourceBoundaryLaw
public import PottsContinuity.Thm3.Touch.FiniteRectangleEmbedding
public import PottsContinuity.DualityExt.PositiveEmbeddedDualEdgeState
public import PottsContinuity.DualityExt.PositiveDualSubgraphEdgeState
public import PottsContinuity.Thm3.Prop4.TiltedBondReflection
public import PottsContinuity.Thm3.Prop4.TiltedSelfDual
public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import Mathlib.Tactic
public import PottsContinuity.PD.RCInfinite.FiniteEnergy

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory
noncomputable section

/-- Genuine crossed-bond index followed by the half-turn and integer shift. -/
def tiltedStripCrossedBond (N : ℕ) (b : LatticeBond) : LatticeBond :=
  ⟨(-b.base.1,(N : ℤ)-b.base.2), match b.axis with
    | .horizontal => .vertical
    | .vertical => .horizontal⟩

local instance tiltedTransportBondCountable : Countable LatticeBond :=
  Countable.of_equiv (LatticeVertex × LatticeAxis)
    { toFun := fun p => ⟨p.1,p.2⟩
      invFun := fun b => (b.base,b.axis)
      left_inv := by rintro ⟨a,x⟩; rfl
      right_inv := by rintro ⟨a,x⟩; rfl }

local instance tiltedTransportActualBondCountable (N : ℕ) (t : ℝ) :
    Countable (TiltedBond N t) := by
  unfold TiltedBond
  infer_instance

end
end PottsContinuity.RSW
