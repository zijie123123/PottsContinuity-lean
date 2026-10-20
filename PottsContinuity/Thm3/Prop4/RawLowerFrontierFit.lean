module

public import PottsContinuity.Thm3.Prop4.RawDualFiniteFit
public import PottsContinuity.Thm3.Prop4.RawRecordedFaceRegion
public import PottsContinuity.Thm3.Prop4.MarkedLowerFrontierCrossing

/-! # Source face regions fit the existing marked lower raw frontier exactly -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- The literal lower-arc sampled raw reveal is the existing marked raw reveal. -/
theorem sampledRawDualReveal_lower_arc_eq (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    sampledRawDualReveal a w h (PlanarTopology.rectangleLowerDualArc a w h u v) A =
      markedLowerDualReveal a w h u v A := by
  have hseeds : Subtype.val '' (markedLowerDualSeeds a w h u v : Set (RectangleDualVertex a w h)) =
      PlanarTopology.rectangleLowerDualArc a w h u v := by
    classical
    ext s
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact (Finset.mem_filter.mp hf).2
    · intro hs
      let f : RectangleDualVertex a w h :=
        ⟨s,PlanarTopology.rectangle_dual_arc_mem_expanded a w h u v s (Or.inl hs)⟩
      refine ⟨f,?_,rfl⟩
      change f ∈ markedLowerDualSeeds a w h u v
      simpa [markedLowerDualSeeds,f] using hs
  rw [← hseeds,sampledRawDualReveal_eq_finite_raw]
  rfl

/-- The lower frontier used by the existing excursion bounds is exactly the
frontier of the source raw lower closed-dual region. -/
theorem markedLowerFrontier_eq_source_raw_frontier (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    markedLowerFrontier a w h u v A =
      rawFaceRegionFrontier a w h (sampledDualSeedRegion a w h A
        (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)) := by
  unfold markedLowerFrontier
  rw [← sampledRawDualReveal_lower_arc_eq a w h u.val v.val A]
  convert recorded_raw_frontier_eq_actual a w h A
    (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) using 1
  congr 1
  ext e
  simp only [Finset.mem_inter]

end
end PottsContinuity.Thm3.Prop4
