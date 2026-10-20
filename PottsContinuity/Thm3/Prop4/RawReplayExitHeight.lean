module

public import PottsContinuity.Thm3.Prop4.RawReplayRegionExit
public import PottsContinuity.Thm3.Prop4.ClampedFaceEndpointHeight
public import PottsContinuity.Thm3.Prop4.TubeRevealedEdges

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology Exploration
noncomputable section
local instance rawReplayExitHeightEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- An omitted induced-mask bond has an actual original endpoint outside
its vertex carrier. -/
theorem rectangle_mask_omitted_endpoint (a : LatticeVertex) (w h : ℕ)
    (T : Set LatticeVertex) (e : (rectangleGraph a w h).edgeSet)
    (he : e ∉ RSW.inducedConfigurationErasure {z : RectangleVertex a w h | z.val ∈ T}
      (Finset.univ : Configuration (rectangleGraph a w h))) :
    ∃ z : RectangleVertex a w h, z ∈ e.val ∧ z.val ∉ T := by
  classical
  by_contra hn
  apply he
  apply (RSW.mem_inducedConfigurationErasure _ _ e).mpr
  exact ⟨Finset.mem_univ _,fun z hz => by simpa only [Set.mem_ofPred_eq] using
    (show z.val ∈ T by by_contra hzT; exact hn ⟨z,hz,hzT⟩)⟩

/-- The first bridge face on the lower reached region has the signed
clamped height forced by an omitted actual raw query. -/
theorem sampledRawDual_masked_replay_exit_height_le
    (a : LatticeVertex) (w h : ℕ) (S : Set LatticeVertex)
    (A B R : Configuration (rectangleGraph a w h)) (T : Set LatticeVertex)
    (hR : sampledRawDualReveal a w h S A ⊆ R) (t b L : ℝ) (ht : |t| ≤ 1)
    (hside : ∀ e ∈ sampledRawDualReveal a w h S A,
      ∀ z : RectangleVertex a w h, z ∈ e.val → z.val ∉ T →
        (z.val.2 : ℝ)-(t*z.val.1+b) ≤ L)
    {x y : LatticeVertex} (hx : sampledDualSeedRegion a w h A S x)
    (hy : ¬sampledDualSeedRegion a w h A S y)
    (hxy : (rectangleSampledClosedDualGraph a w h
      (replayRevealedState (rectangleGraph a w h) R ⟨A ∩ R,Finset.inter_subset_right⟩ B ∩
        RSW.inducedConfigurationErasure {z : RectangleVertex a w h | z.val ∈ T}
          (Finset.univ : Configuration (rectangleGraph a w h)))).Adj x y) :
    (rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).re+b) ≤ L+1 := by
  obtain ⟨d,hdx,hdS,_,hdM⟩ := sampledRawDual_masked_replay_exit a w h S A B R _ hR hx hy hxy
  obtain ⟨z,hzd,hzT⟩ := rectangle_mask_omitted_endpoint a w h T d.primalEdge hdM
  have hz := hside d.primalEdge hdS z hzd hzT
  have hf := (abs_le.mp (rectangleClampedFace_endpoint_height_distance_le a w h d z hzd x hdx t b ht)).2
  linarith only [hz,hf]

/-- The upper signed version uses the very same unchanged raw record. -/
theorem sampledRawDual_masked_replay_exit_height_ge
    (a : LatticeVertex) (w h : ℕ) (S : Set LatticeVertex)
    (A B R : Configuration (rectangleGraph a w h)) (T : Set LatticeVertex)
    (hR : sampledRawDualReveal a w h S A ⊆ R) (t b L : ℝ) (ht : |t| ≤ 1)
    (hside : ∀ e ∈ sampledRawDualReveal a w h S A,
      ∀ z : RectangleVertex a w h, z ∈ e.val → z.val ∉ T →
        L ≤ (z.val.2 : ℝ)-(t*z.val.1+b))
    {x y : LatticeVertex} (hx : sampledDualSeedRegion a w h A S x)
    (hy : ¬sampledDualSeedRegion a w h A S y)
    (hxy : (rectangleSampledClosedDualGraph a w h
      (replayRevealedState (rectangleGraph a w h) R ⟨A ∩ R,Finset.inter_subset_right⟩ B ∩
        RSW.inducedConfigurationErasure {z : RectangleVertex a w h | z.val ∈ T}
          (Finset.univ : Configuration (rectangleGraph a w h)))).Adj x y) :
    L-1 ≤ (rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).re+b) := by
  obtain ⟨d,hdx,hdS,_,hdM⟩ := sampledRawDual_masked_replay_exit a w h S A B R _ hR hx hy hxy
  obtain ⟨z,hzd,hzT⟩ := rectangle_mask_omitted_endpoint a w h T d.primalEdge hdM
  have hz := hside d.primalEdge hdS z hzd hzT
  have hf := (abs_le.mp (rectangleClampedFace_endpoint_height_distance_le a w h d z hzd x hdx t b ht)).1
  linarith only [hz,hf]

end
end PottsContinuity.Thm3.Prop4
