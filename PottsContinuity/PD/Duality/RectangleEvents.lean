-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/RectangleEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/RectangleEvents.lean`.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.PD.FK.Model
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PD.FK

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

/-- Actual left-to-right open crossing of the full induced lattice rectangle.
The side endpoints are included as vertices; connectivity uses open graph
edges only and never boundary identifications. -/
def rectangleHorizontalCrossingEvent : Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleVertex a w h,
    u.val ∈ rectangleLeftSide a w h ∧ v.val ∈ rectangleRightSide a w h ∧
      ActualConnected (rectangleGraph a w h) A u v}

attribute [local instance] configurationMeasurableSpace

end
end PottsContinuity.PD.FK
