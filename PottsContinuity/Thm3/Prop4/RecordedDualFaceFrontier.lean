module

public import PottsContinuity.Thm3.Prop4.RecordedSampledDualGraph
public import PottsContinuity.Thm3.Prop4.SampledStarPorts

/-!
# The original-edge frontier of a recorded closed-dual region

The region consists of actual recorded closed-dual walks from the supplied
face set. Its frontier retains original edge labels. Every retained frontier
edge is recorded open and has an incident region face with a recorded arm.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section
local instance recordedDualFaceFrontierEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Region reached from the specified faces using only recorded closed
sampled original bonds. The seed face itself is included by the empty walk. -/
def recordedDualReachableFrom (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (f : LatticeVertex) : Prop :=
  ∃ s ∈ L, (recordedSampledClosedDualGraph a w h R B).Reachable s f

/-- Revealed original edges whose two incident dual faces have different
membership in the recorded closed-dual region. -/
def recordedDualFaceFrontier (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex) :
    Configuration (rectangleGraph a w h) := by
  classical
  exact R.filter fun e =>
    recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).source ≠
    recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).target

/-- A recorded closed bond joins its two incident region tests. -/
theorem recordedDualReachableFrom_iff_of_closed_bond (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (e : (rectangleGraph a w h).edgeSet) (heR : e ∈ R) (heB : e ∉ B) :
    recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).source ↔
    recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).target := by
  have hadj : (recordedSampledClosedDualGraph a w h R B).Adj
      (rectangleCrossingDualBond a w h e).source (rectangleCrossingDualBond a w h e).target :=
    ⟨rectanglePrimalDualEdgeEquiv a w h e,heR,heB,Or.inl ⟨rfl,rfl⟩⟩
  constructor
  · rintro ⟨s,hs,hreach⟩
    exact ⟨s,hs,hreach.trans ⟨hadj.toWalk⟩⟩
  · rintro ⟨s,hs,hreach⟩
    exact ⟨s,hs,hreach.trans ⟨hadj.symm.toWalk⟩⟩

/-- Every actual original-edge frontier bond is open in the recorded state. -/
theorem recordedDualFaceFrontier_subset_recorded (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex) :
    recordedDualFaceFrontier a w h R B L ⊆ B := by
  classical
  intro e he
  obtain ⟨heR,hneq⟩ := Finset.mem_filter.mp he
  by_contra heB
  exact hneq (propext (recordedDualReachableFrom_iff_of_closed_bond a w h R B L e heR heB))

/-- Each endpoint of a frontier original bond has a genuine sampled star
port reached from L by an actual recorded closed-dual walk. No exterior cap
or boundary completion is introduced. -/
theorem recorded_dual_arm_at_frontier_bond (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (e : (rectangleGraph a w h).edgeSet) (he : e ∈ recordedDualFaceFrontier a w h R B L)
    (z : RectangleVertex a w h)
    (hz : (rectanglePrimalEdgeBond a w h e).source = z.val ∨
      (rectanglePrimalEdgeBond a w h e).target = z.val) :
    ∃ f ∈ sampledStarFacePorts a w h z, ∃ s ∈ L,
      Nonempty ((recordedSampledClosedDualGraph a w h R B).Walk s f) := by
  classical
  have hneq := (Finset.mem_filter.mp he).2
  have hsome : recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).source ∨
      recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).target := by
    by_cases hs : recordedDualReachableFrom a w h R B L (rectangleCrossingDualBond a w h e).source
    · exact Or.inl hs
    · right
      by_contra ht
      exact hneq (propext (iff_of_false hs ht))
  let b : RectanglePrimalBond a w h :=
    ⟨rectanglePrimalEdgeBond a w h e,rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  have hsource : (rectangleCrossingDualBond a w h e).source = b.val.faceBase false := by
    exact rectangleDualEdgeSource_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  have htarget : (rectangleCrossingDualBond a w h e).target = b.val.faceBase true := by
    exact rectangleDualEdgeTarget_faceBase a w h (rectanglePrimalDualEdgeEquiv a w h e)
  rcases hsome with ⟨s,hs,hp⟩ | ⟨s,hs,hp⟩
  · exact ⟨_,⟨b,hz,Or.inl hsource⟩,s,hs,hp⟩
  · exact ⟨_,⟨b,hz,Or.inr htarget⟩,s,hs,hp⟩

end
end PottsContinuity.Thm3.Prop4
