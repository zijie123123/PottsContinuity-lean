module

public import PottsContinuity.Thm3.Prop4.SampledRawDualRegion
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

/-! # The exact stopped law for the two uncompleted marked arc explorations -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial Exploration
noncomputable section
local instance rawMarkedStoppedEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The raw top and bottom exploration is the union of their face regions. -/
def sourceMarkedRawReveal (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) : RevealMap (G := rectangleGraph a w h) :=
  sampledRawDualReveal a w h
    (PlanarTopology.rectangleLowerDualArc a w h u.val v.val ∪
      PlanarTopology.rectangleUpperDualArc a w h u.val v.val)

/-- The source remaining graph keeps precisely the unqueried original bonds. -/
def sourceMarkedRawDomain (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    SimpleGraph (RectangleVertex a w h) :=
  edgeRestriction (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)

/-- This source record queries exactly the two raw explorations. -/
theorem sourceMarkedRawReveal_eq_union (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    sourceMarkedRawReveal a w h u v A =
      sampledRawDualReveal a w h (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) A ∪
      sampledRawDualReveal a w h (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) A :=
  sampledRawDualReveal_union a w h _ _ A

/-- No success event is needed for the stopping property of the raw record. -/
theorem sourceMarkedRawReveal_stable (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ sourceMarkedRawReveal a w h u v A =
      A ∩ sourceMarkedRawReveal a w h u v A) :
    sourceMarkedRawReveal a w h u v C = sourceMarkedRawReveal a w h u v A :=
  sampledRawDualReveal_stable a w h _ A C hagree

/-- The exact conditional law on ALL remaining original edges under the
uncompleted source record. Hole components are retained in this identity. -/
theorem law_filter_sourceMarkedRawRecord_map_remaining (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (θ : Parameters)
    (ξ : BoundaryCondition (RectangleVertex a w h))
    (A : Configuration (rectangleGraph a w h)) :
    ((law (rectangleGraph a w h) θ ξ).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ ξ _ (revealRecordConfiguration _ A))).map
        (fun C => (configurationSplitEquiv (rectangleGraph a w h)
          (sourceMarkedRawReveal a w h u v A) C).1) =
      remainingLaw (rectangleGraph a w h) θ
        (frozenBoundary ξ (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val)
        (sourceMarkedRawReveal a w h u v A) :=
  law_filter_revealRecord_map_remaining θ ξ _ (sourceMarkedRawReveal_stable a w h u v) A

end
end PottsContinuity.Thm3.Prop4
