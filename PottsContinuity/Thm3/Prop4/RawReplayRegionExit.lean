module

public import PottsContinuity.Thm3.Prop4.RawReplayDualBridge

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology Exploration
noncomputable section
local instance rawReplayRegionExitEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Leaving an actual reached face region along a masked replay dual edge
crosses an original open queried bond omitted by the mask. -/
theorem sampledRawDual_masked_replay_exit (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A B R M : Configuration (rectangleGraph a w h))
    (hR : sampledRawDualReveal a w h S A ⊆ R)
    {x y : LatticeVertex} (hx : sampledDualSeedRegion a w h A S x)
    (hy : ¬sampledDualSeedRegion a w h A S y)
    (hxy : (rectangleSampledClosedDualGraph a w h
      (replayRevealedState (rectangleGraph a w h) R ⟨A ∩ R,Finset.inter_subset_right⟩ B ∩ M)).Adj x y) :
    ∃ d : RectangleDualEdgeCarrier a w h,
      (x = d.crossingBond.source ∨ x = d.crossingBond.target) ∧
      d.primalEdge ∈ sampledRawDualReveal a w h S A ∧
      d.primalEdge ∈ A ∧ d.primalEdge ∉ M := by
  classical
  obtain ⟨d,hd,hends⟩ := hxy
  have hdx : x = d.crossingBond.source ∨ x = d.crossingBond.target :=
    hends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hquery : d.primalEdge ∈ sampledRawDualReveal a w h S A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← d.crossingBond_eq]
    exact hdx.elim (fun he => Or.inl (he ▸ hx)) (fun he => Or.inr (he ▸ hx))
  have hopen : d.primalEdge ∈ A := by
    by_contra hn
    exact hy (sampledDualSeedRegion_step a w h A S ⟨d,hn,hends⟩ hx)
  refine ⟨d,hdx,hquery,hopen,?_⟩
  intro hm
  apply hd
  exact (Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mpr
    ⟨Finset.mem_union_right _ ((Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mpr
      ⟨hopen,hR hquery⟩),hm⟩

end
end PottsContinuity.Thm3.Prop4
