module

public import PottsContinuity.Thm3.Prop4.SampledRawDualRegion
public import PottsContinuity.Thm3.Prop4.RecordedDualFaceFrontier

/-! # Actual raw face regions agree with their recorded face regions -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- Every actual closed step out of a reached face has already been queried. -/
theorem sampledRawDualReveal_queries_step (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex)
    {x y : LatticeVertex} (d : RectangleDualEdgeCarrier a w h)
    (hends : (x = d.crossingBond.source ∧ y = d.crossingBond.target) ∨
      (x = d.crossingBond.target ∧ y = d.crossingBond.source))
    (hx : sampledDualSeedRegion a w h A S x) :
    d.primalEdge ∈ sampledRawDualReveal a w h S A := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [← d.crossingBond_eq]
  rcases hends with ⟨hxs,_⟩ | ⟨hxt,_⟩
  · exact Or.inl (hxs ▸ hx)
  · exact Or.inr (hxt ▸ hx)

/-- The full actual reached region is EXACTLY determined by the recorded
sampled closed bonds, with the same seed set and original face labels. -/
theorem sampledDualSeedRegion_iff_recorded_raw (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) (f : LatticeVertex) :
    sampledDualSeedRegion a w h A S f ↔
      recordedDualReachableFrom a w h (sampledRawDualReveal a w h S A)
        (A ∩ sampledRawDualReveal a w h S A) S f := by
  constructor
  · rintro ⟨s,hs,⟨p⟩⟩
    have liftWalk {x y} (p : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk x y) :
        sampledDualSeedRegion a w h A S x →
        (recordedSampledClosedDualGraph a w h (sampledRawDualReveal a w h S A)
          (A ∩ sampledRawDualReveal a w h S A)).Reachable x y := by
      induction p with
      | nil => exact fun _ => SimpleGraph.Reachable.refl _
      | cons hxy p ih =>
        intro hx
        obtain ⟨d,hd,hends⟩ := hxy
        have heR := sampledRawDualReveal_queries_step a w h A S d hends hx
        have heB : d.primalEdge ∉ A ∩ sampledRawDualReveal a w h S A := by
          intro he
          erw [Finset.mem_inter] at he
          exact hd he.1
        have hrecorded : (recordedSampledClosedDualGraph a w h (sampledRawDualReveal a w h S A)
            (A ∩ sampledRawDualReveal a w h S A)).Adj _ _ := ⟨d,heR,heB,hends⟩
        exact hrecorded.reachable.trans
          (ih (sampledDualSeedRegion_step a w h A S ⟨d,hd,hends⟩ hx))
    exact ⟨s,hs,liftWalk p ⟨s,hs,SimpleGraph.Reachable.refl s⟩⟩
  · rintro ⟨s,hs,hp⟩
    have hle := recordedSampledClosedDualGraph_le_state a w h
      (sampledRawDualReveal a w h S A) (A ∩ sampledRawDualReveal a w h S A) A (by ext e; simp only [Finset.mem_inter])
    exact ⟨s,hs,hp.mono hle⟩

/-- The old recorded frontier is the actual raw-region frontier. No filling
or larger observation is involved in this identification. -/
theorem recorded_raw_frontier_eq_actual (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) :
    recordedDualFaceFrontier a w h (sampledRawDualReveal a w h S A)
      (A ∩ sampledRawDualReveal a w h S A) S =
      rawFaceRegionFrontier a w h (sampledDualSeedRegion a w h A S) := by
  classical
  ext e
  have hs := propext (sampledDualSeedRegion_iff_recorded_raw a w h A S
    (rectangleCrossingDualBond a w h e).source)
  have ht := propext (sampledDualSeedRegion_iff_recorded_raw a w h A S
    (rectangleCrossingDualBond a w h e).target)
  simp only [recordedDualFaceFrontier,rawFaceRegionFrontier,Finset.mem_filter,
    Finset.mem_univ,true_and]
  rw [← hs,← ht]
  constructor
  · exact fun h => h.2
  · intro hneq
    refine ⟨?_,hneq⟩
    apply rawFaceRegionFrontier_subset_reveal a w h _
    simpa only [rawFaceRegionFrontier,Finset.mem_filter,Finset.mem_univ,true_and] using hneq

end
end PottsContinuity.Thm3.Prop4
