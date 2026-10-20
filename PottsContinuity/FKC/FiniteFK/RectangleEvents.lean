-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Rectangle
public import PottsContinuity.FKC.FiniteFK.Wiring
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

/-- Actual left-to-right open crossing of the full induced lattice rectangle.
The side endpoints are included as vertices; connectivity uses open graph
edges only and never boundary identifications. -/
def rectangleHorizontalCrossingEvent : Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleVertex a w h,
    u.val ∈ rectangleLeftSide a w h ∧ v.val ∈ rectangleRightSide a w h ∧
      ActualConnected (rectangleGraph a w h) A u v}

/-- Actual bottom-to-top open crossing of the full induced lattice rectangle. -/
def rectangleVerticalCrossingEvent : Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleVertex a w h,
    u.val ∈ rectangleBottomSide a w h ∧ v.val ∈ rectangleTopSide a w h ∧
      ActualConnected (rectangleGraph a w h) A u v}

attribute [local instance] configurationMeasurableSpace

/-- Restrict a larger rectangle configuration to the genuine induced inner graph. -/
def rectangleConfigurationRestriction {b : LatticeVertex} {w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    Configuration (rectangleGraph b w' h') → Configuration (rectangleGraph a w h) :=
  embeddedConfigurationRestriction (rectangleGraph a w h) (rectangleGraph b w' h')
    (rectangleVertexEmbedding hrect) (rectangleGraph_map_rectangleVertexEmbedding hrect)

/-- Membership in the restricted left-to-right event tests only the inner graph. -/
def rectangleInnerHorizontalCrossingEvent {b : LatticeVertex} {w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    Set (Configuration (rectangleGraph b w' h')) :=
  {A | rectangleConfigurationRestriction a w h hrect A ∈ rectangleHorizontalCrossingEvent a w h}

end
end PottsContinuity.FKC.FiniteFK
