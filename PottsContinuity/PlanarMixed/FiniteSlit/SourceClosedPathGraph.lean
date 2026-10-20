module

public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleSeparatePathBound
public import PottsContinuity.PlanarMixed.EmbeddedBoundaryLower
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutActive
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceActiveCarrier
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PD.FK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section
local instance sourceClosedPathGraphEdgeEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- All original source bonds internal to either of the marked path supports. -/
def sourcePathArcBonds (w h : ℕ) (P : SourceWalkPair (rectangleGraph (0,0) w h)) :
    Configuration (rectangleGraph (0,0) w h) :=
  internalBonds (rectangleGraph (0,0) w h) {z | z ∈ P.first.support} ∪
    internalBonds (rectangleGraph (0,0) w h) {z | z ∈ P.second.support}

/-- The closed source band: the active interior together with all original
bonds internal to either marked path. All other revealed bonds stay deleted. -/
def sourceClosedPathGraph (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h)) :=
  edgeRestriction (rectangleGraph (0,0) w h)
    (sourceExteriorReveal w h x P.secondEnd.val.2
      (Subtype.val '' {z | z ∈ P.first.support})
      (Subtype.val '' {z | z ∈ P.second.support}) \ sourcePathArcBonds w h P)

/-- Every closed-band bond is an original source-rectangle bond. -/
theorem sourceClosedPathGraph_le_rectangle (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h)) :
    sourceClosedPathGraph w h x P ≤ rectangleGraph (0,0) w h :=
  edgeRestriction_le _ _

end
end PottsContinuity.PlanarMixed.FiniteSlit
