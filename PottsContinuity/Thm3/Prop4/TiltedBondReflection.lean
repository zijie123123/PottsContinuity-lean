module

public import PottsContinuity.Thm3.Prop4.TiltedReflection
public import PottsContinuity.PD.Duality.PrimalDualSegments

/-!
# Reflection of the actual primal bonds and their adjacent dual faces

The primal normalized bond base and dual face label have different shifts.
The identities here retain both, including every digital boundary bond.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK.Medial

/-- A genuine original bond of the induced tilted strip. -/
def TiltedBond (N : ℕ) (t : ℝ) :=
  {b : LatticeBond // b.source ∈ tiltedStripVertices N t ∧ b.target ∈ tiltedStripVertices N t}

/-- Its actual original-edge index, with no extra dual or boundary edge. -/
def tiltedBondEdge (N : ℕ) (t : ℝ) (b : TiltedBond N t) : (tiltedStripGraph N t).edgeSet :=
  ⟨s(⟨b.val.source,b.property.1⟩,⟨b.val.target,b.property.2⟩),
    (tiltedStripGraph N t).mem_edgeSet.mpr b.val.adjacent⟩

end PottsContinuity.Thm3.Prop4
