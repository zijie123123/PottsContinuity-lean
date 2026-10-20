module

public import PottsContinuity.Thm3.Prop4.MarkedFaceFrontierConnectivity
public import PottsContinuity.Thm3.Prop4.MarkedUpperRawAccess
public import PottsContinuity.Thm3.Prop4.MarkedJointRawReveal
public import PottsContinuity.Thm3.Prop4.SourceMiddleDomain
public import PottsContinuity.Thm3.Prop4.SourceRevealExtension
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.Thm3.Prop4.ObservedSourceCompletion
public import PottsContinuity.Thm3.Prop4.MarkedLowerFrontierCrossing

/-! # The exact sampled point-mark complementary-arc alternative -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- If the original prescribed side marks are disconnected, an ACTUAL
sampled closed-dual walk joins their complementary exterior arcs. -/
theorem sampled_dual_arc_walk_of_marked_disconnection
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A : Configuration (rectangleGraph a w h))
    (hA : ¬ActualConnected (rectangleGraph a w h) A u v) :
    ∃ s ∈ PlanarTopology.rectangleLowerDualArc a w h u.val v.val,
      ∃ t ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val,
        Nonempty ((PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk s t) := by
  classical
  by_contra hn
  have hl : ∀ f ∈ PlanarTopology.rectangleLowerDualArc a w h u.val v.val,
      sampledDualSeedRegion a w h A (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) f :=
    fun f hf => ⟨f,hf,SimpleGraph.Reachable.refl _⟩
  have ht : ∀ f ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val,
      ¬sampledDualSeedRegion a w h A (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) f := by
    rintro f hf ⟨s,hs,hconn⟩
    exact hn ⟨s,hs,f,hf,hconn⟩
  have hconn := rawFaceRegionFrontier_connects_of_marked_arc_labels a w h hw hh u v hu hv _ hl ht
  exact hA (hconn.mono (openGraph_mono (sampledRawDual_frontier_open a w h A _)))

end
end PottsContinuity.Thm3.Prop4
