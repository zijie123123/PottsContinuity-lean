module

public import PottsContinuity.Thm3.Prop4.RawCentralReferenceComparison
public import PottsContinuity.Thm3.Prop4.FrozenReplayComparison

/-! # Literal raw replay stays in the edge-defined marked union -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
local instance rawCentralReplayRetentionEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A replay edge cannot leave the whole edge-defined marked union. Fresh
edges stay in their remaining component; recorded edges stay in their actual
recorded class. No access-defined middle or tube bound is required. -/
theorem sourceMarkedRawCentralVertices_replay_edge_closed
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A B : Configuration (rectangleGraph a w h))
    (x : RectangleVertex a w h) (hx : x ∈ sourceMarkedRawCentralVertices a w h u v A)
    (y : RectangleVertex a w h)
    (hxy : (openGraph (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B)).Adj x y) :
    y ∈ sourceMarkedRawCentralVertices a w h u v A := by
  classical
  obtain ⟨e,he,hev⟩ := (openGraph_adj _ _ x y).mp hxy
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨heB,hn⟩ := Finset.mem_sdiff.mp he
    have hrem : (sourceMarkedRawDomain a w h u v A).Adj x y := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨(rectangleGraph a w h).mem_edgeSet.mp (hev ▸ e.property),?_⟩
      rw [← hev,coe_mem_openEdges_iff]
      exact hn
    exact sourceMarkedRawCentralVertices_edge_closed a w h u v A x hx y hrem
  · have hrec : (openGraph (rectangleGraph a w h)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val).Adj x y :=
      (openGraph_adj _ _ x y).mpr ⟨e,he,hev⟩
    apply sourceMarkedRawCentralVertices_boundary_closed a w h hw hh u v hu A x hx y
    exact actualConnected_component (rectangleGraph a w h) (BoundaryCondition.free ∅)
      (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A).val hrec.reachable

/-- Every vertex of every actual raw replay walk starting at u belongs to
the retained edge-defined union. In particular restricting to that union
loses no step of a tube-confined replay walk. -/
theorem sourceMarkedRaw_replay_walk_support_central
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A B : Configuration (rectangleGraph a w h))
    {z : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B)).Walk u z) :
    ∀ x ∈ p.support, x ∈ sourceMarkedRawCentralVertices a w h u v A := by
  have hclosed := sourceMarkedRawCentralVertices_replay_edge_closed a w h hw hh u v hu A B
  have gen {s t} (q : (openGraph (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B)).Walk s t)
      (hs : s ∈ sourceMarkedRawCentralVertices a w h u v A) :
      ∀ x ∈ q.support, x ∈ sourceMarkedRawCentralVertices a w h u v A := by
    induction q with
    | nil =>
      intro x hx
      have heq := List.mem_singleton.mp hx
      subst x
      exact hs
    | @cons s c t hsc q ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs
      · exact ih (hclosed s hs c hsc) x hx
  exact gen p (sourceMarkedRawCentralVertices_mark a w h u v A)

end
end PottsContinuity.Thm3.Prop4
