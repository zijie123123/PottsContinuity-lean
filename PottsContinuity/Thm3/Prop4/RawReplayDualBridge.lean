module

public import PottsContinuity.Thm3.Prop4.RegionBridgeExtraction
public import PottsContinuity.Thm3.Prop4.RawCentralRestoredWalk
public import PottsContinuity.Thm3.Prop4.MarkedArcAlternativeProved

/-! # Transferring a masked raw-replay dual bridge back to the reference -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration PlanarTopology
noncomputable section
local instance rawReplayDualBridgeEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The actual lower reached dual face region of the unchanged source sample. -/
def sourceMarkedRawLowerFaces (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) : Set LatticeVertex :=
  {f | sampledDualSeedRegion a w h A (rectangleLowerDualArc a w h u.val v.val) f}

/-- The actual upper reached dual face region of the unchanged source sample. -/
def sourceMarkedRawUpperFaces (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) : Set LatticeVertex :=
  {f | sampledDualSeedRegion a w h A (rectangleUpperDualArc a w h u.val v.val) f}

/-- Each queried original bond closed in the source has both dual endpoints
in ONE of the actual reached regions. No frontier-only query claim is used. -/
theorem sourceMarkedRaw_closed_query_faces (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (e : (rectangleGraph a w h).edgeSet) (he : e ∈ sourceMarkedRawReveal a w h u v A) (hn : e ∉ A) :
    ((rectangleCrossingDualBond a w h e).source ∈ sourceMarkedRawLowerFaces a w h u v A ∧
      (rectangleCrossingDualBond a w h e).target ∈ sourceMarkedRawLowerFaces a w h u v A) ∨
    ((rectangleCrossingDualBond a w h e).source ∈ sourceMarkedRawUpperFaces a w h u v A ∧
      (rectangleCrossingDualBond a w h e).target ∈ sourceMarkedRawUpperFaces a w h u v A) := by
  rw [sourceMarkedRawReveal_eq_union] at he
  rcases Finset.mem_union.mp he with he | he
  · exact Or.inl (sampledRawDual_closed_faces a w h A _ e he hn)
  · exact Or.inr (sampledRawDual_closed_faces a w h A _ e he hn)

/-- After removing edges internal to either reached face region, EVERY
remaining sampled closed-dual edge of masked FULL RAW replay is closed under
the SAME masked reference. The mask may be any original-edge carrier. -/
theorem sourceMarkedRaw_masked_dual_bridge_le_reference (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A B M : Configuration (rectangleGraph a w h)) :
    regionBridgeGraph (rectangleSampledClosedDualGraph a w h
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∩ M))
      (sourceMarkedRawLowerFaces a w h u v A) (sourceMarkedRawUpperFaces a w h u v A) ≤
      rectangleSampledClosedDualGraph a w h (B ∩ M) := by
  classical
  rintro x y ⟨⟨d,hd,hends⟩,hP,hQ⟩
  refine ⟨d,?_,hends⟩
  intro heBM
  obtain ⟨heB,heM⟩ := (Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mp heBM
  by_cases heR : d.primalEdge ∈ sourceMarkedRawReveal a w h u v A
  · have hnA : d.primalEdge ∉ A := by
      intro heA
      apply hd
      exact (Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mpr ⟨Finset.mem_union_right _ ((Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mpr ⟨heA,heR⟩),heM⟩
    have hboth := sourceMarkedRaw_closed_query_faces a w h u v A d.primalEdge heR hnA
    rw [← d.crossingBond_eq] at hboth
    rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hboth.elim hP hQ
    · exact hboth.elim (fun h => hP h.symm) (fun h => hQ h.symm)
  · exact hd ((Finset.mem_inter (α := (rectangleGraph a w h).edgeSet)).mpr
      ⟨Finset.mem_union_left _ ((Finset.mem_sdiff (α := (rectangleGraph a w h).edgeSet)).mpr ⟨heB,heR⟩),heM⟩)

/-- A genuine marked disconnection in masked raw replay supplies a bridge
between the two actual reached regions. Its edges transfer to the masked
reference by the preceding theorem; internal region excursions are removed. -/
theorem sourceMarkedRaw_dual_bridge_of_masked_disconnection
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A B M : Configuration (rectangleGraph a w h))
    (hdis : ¬ActualConnected (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∩ M) u v) :
    ∃ x ∈ sourceMarkedRawLowerFaces a w h u v A,
      ∃ y ∈ sourceMarkedRawUpperFaces a w h u v A,
      Nonempty ((regionBridgeGraph (rectangleSampledClosedDualGraph a w h
        (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
          (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∩ M))
          (sourceMarkedRawLowerFaces a w h u v A) (sourceMarkedRawUpperFaces a w h u v A)).Walk x y) := by
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := sampled_dual_arc_walk_of_marked_disconnection a w h hw hh u v hu hv _ hdis
  exact regionBridgeGraph_reachable_between_regions _ _ _
    ⟨s,hs,SimpleGraph.Reachable.refl _⟩ ⟨t,ht,SimpleGraph.Reachable.refl _⟩ ⟨p⟩

end
end PottsContinuity.Thm3.Prop4
