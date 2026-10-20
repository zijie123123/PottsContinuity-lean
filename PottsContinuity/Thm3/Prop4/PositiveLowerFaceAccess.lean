module

public import PottsContinuity.Thm3.Prop4.RectangleSampledDualBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Nonempty trace-complement access to an incident reached face

Appending the queried bond avoids a zero-length interpolation corner case.
The bond is absent from the primal trace; it need not be closed in the
original sample, since the access is constructed in the TRACE complement.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section

/-- An incident face reached by actual closed dual bonds gives a POSITIVE
finite dual walk in the trace complement ending at one of the same bond's
incident faces. All steps still cross original sampled bonds. -/
theorem positive_trace_complement_access_of_incident_reached_face
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (htrace : rectangleTraceConfiguration a w h p ⊆ A)
    (L : Set LatticeVertex) (hL : L ⊆ (rectangleDualExpanded a w h : Set LatticeVertex))
    (e : RectangleDualEdgeCarrier a w h)
    (he : e.primalEdge ∉ rectangleTraceConfiguration a w h p)
    (hreach : (∃ s ∈ L, (rectangleSampledClosedDualGraph a w h A).Reachable s e.crossingBond.source) ∨
      (∃ s ∈ L, (rectangleSampledClosedDualGraph a w h A).Reachable s e.crossingBond.target)) :
    ∃ s : RectangleDualVertex a w h, s.val ∈ L ∧
      ∃ t : RectangleDualVertex a w h,
        (t.val = e.crossingBond.source ∨ t.val = e.crossingBond.target) ∧
        ∃ q : (openGraph (rectangleDualGraph a w h)
          (rectangleDualConfiguration a w h (rectangleTraceConfiguration a w h p))).Walk s t,
          0 < q.length := by
  have hle : rectangleSampledClosedDualGraph a w h A ≤
      rectangleSampledClosedDualGraph a w h (rectangleTraceConfiguration a w h p) := by
    rintro x y ⟨d,hd,hends⟩
    exact ⟨d,fun hh => hd (htrace hh),hends⟩
  let f := rectangleDualEdgeSource a w h e
  let g := rectangleDualEdgeTarget a w h e
  have hadj : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h (rectangleTraceConfiguration a w h p))).Adj f g := by
    apply rectangleSampledClosedDualGraph_adj_finite
    exact ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  have lift (t : RectangleDualVertex a w h)
      (ht : ∃ s ∈ L, (rectangleSampledClosedDualGraph a w h A).Reachable s t.val) :
      ∃ s : RectangleDualVertex a w h, s.val ∈ L ∧
        Nonempty ((openGraph (rectangleDualGraph a w h)
          (rectangleDualConfiguration a w h (rectangleTraceConfiguration a w h p))).Walk s t) := by
    obtain ⟨s,hs,⟨r⟩⟩ := ht
    refine ⟨⟨s,hL hs⟩,hs,?_⟩
    exact rectangleSampledClosedDualGraph_walk_finite a w h _ (r.mapLe hle) (hL hs) t.property
  rcases hreach with hreach | hreach
  · obtain ⟨s,hs,⟨r⟩⟩ := lift f hreach
    refine ⟨s,hs,g,Or.inr rfl,r.append hadj.toWalk,?_⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]
    omega
  · obtain ⟨s,hs,⟨r⟩⟩ := lift g hreach
    refine ⟨s,hs,f,Or.inl rfl,r.append hadj.symm.toWalk,?_⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]
    omega

end
end PottsContinuity.Thm3.Prop4
