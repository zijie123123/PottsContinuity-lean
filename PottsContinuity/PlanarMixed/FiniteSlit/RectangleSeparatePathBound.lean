module

public import PottsContinuity.PlanarMixed.FiniteSlit.FixedPrefixRecord
public import PottsContinuity.PlanarMixed.FiniteSlit.RectanglePrefixCrosscuts
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRectangleEmbedding
public import PottsContinuity.PlanarMixed.EmbeddedBoundaryLower
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rectangleSeparatePathBoundEdgeEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The static retained-path geometry has genuinely disjoint marked supports. -/
theorem RetainedRectanglePathGeometry.supports_disjoint
    {w h : ℕ} {x : ℤ} {P : SourceWalkPair (rectangleGraph (0,0) w h)}
    (hgeometry : RetainedRectanglePathGeometry w h x P) :
    Disjoint {z | z ∈ P.first.support} {z | z ∈ P.second.support} := by
  rcases hgeometry with ⟨_,_,_,_,_,_,_,_,_,_,hdis,_⟩
  exact Set.disjoint_left.mpr hdis

/-- The actual two path supports are wired as separate classes, free elsewhere. -/
def sourceSeparatePathBoundary (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h))
    (hgeometry : RetainedRectanglePathGeometry w h x P) :=
  twoBlockBoundary {z | z ∈ P.first.support} {z | z ∈ P.second.support}
    hgeometry.supports_disjoint

end
end PottsContinuity.PlanarMixed.FiniteSlit
