-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripConditionalBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import Mathlib.Tactic
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopBoundary
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability

attribute [local instance] configurationMeasurableSpace

noncomputable section

local instance horizontalStripConditionalInnerFintype (M n : ℕ) :
    Fintype (rectangleGraph (-(M : ℤ), 0) (2 * M) (2 * n)).edgeSet :=
  Fintype.ofFinite _
local instance horizontalStripConditionalOuterFintype (N n : ℕ) :
    Fintype (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).edgeSet :=
  Fintype.ofFinite _
local instance horizontalStripConditionalOuterDecidableEq (N n : ℕ) :
    DecidableEq (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).edgeSet :=
  Classical.decEq _

/-- The top row together with the two vertical sides of the strip rectangle. -/
def horizontalStripTopSidesSet (M n : ℕ) :
    Set (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :=
  {v | v.val.2 = (2 * n : ℤ) ∨ v.val.1 = -(M : ℤ) ∨ v.val.1 = (M : ℤ)}

def horizontalStripTopSidesBoundary (M n : ℕ) :
    BoundaryCondition (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :=
  BoundaryCondition.wired (horizontalStripTopSidesSet M n)

end
end PottsContinuity.FKC.FiniteFK
