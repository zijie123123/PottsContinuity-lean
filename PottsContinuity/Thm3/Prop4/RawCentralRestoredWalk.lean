module

public import PottsContinuity.Thm3.Prop4.RawCentralRestoration

/-! # Confined full raw replay walks survive literal central restoration -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
local instance rawCentralRestoredWalkEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The SAME full raw replay walk can be read in the actual central-law
restoration without losing confinement or changing any original open step. -/
theorem sourceMarkedRaw_replay_walk_to_centralRestoration
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A B : Configuration (rectangleGraph a w h)) (T : Set LatticeVertex)
    {z : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B)).Walk u z)
    (hp : ∀ x ∈ p.support, x.val ∈ T) :
    ∃ q : (openGraph (rectangleGraph a w h)
      (sourceMarkedRawCentralRestoration a w h u v A
        (sourceMarkedRawCentralRestriction a w h u v A B))).Walk u z,
      ∀ x ∈ q.support, x.val ∈ T := by
  classical
  let S := sourceMarkedRawCentralVertices a w h u v A
  let F := openGraph (rectangleGraph a w h)
    (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
      (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B)
  let H := openGraph (rectangleGraph a w h)
    (sourceMarkedRawCentralRestoration a w h u v A (sourceMarkedRawCentralRestriction a w h u v A B))
  have hs := sourceMarkedRaw_replay_walk_support_central a w h hw hh u v hu A B p
  let f : F.induce S →g H :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        obtain ⟨e,he,hev⟩ := (openGraph_adj _ _ x.val y.val).mp hxy
        apply (openGraph_adj _ _ x.val y.val).mpr
        refine ⟨e,?_,hev⟩
        rcases Finset.mem_union.mp he with he | he
        · apply Finset.mem_union_right
          obtain ⟨heB,hn⟩ := Finset.mem_sdiff.mp he
          have hrem : (sourceMarkedRawDomain a w h u v A).Adj x.val y.val := by
            apply SimpleGraph.deleteEdges_adj.mpr
            refine ⟨(rectangleGraph a w h).mem_edgeSet.mp (hev ▸ e.property),?_⟩
            rw [← hev,coe_mem_openEdges_iff]
            exact hn
          let d : (sourceMarkedRawCentralGraph a w h u v A).edgeSet :=
            ⟨s(x,y),(sourceMarkedRawCentralGraph a w h u v A).mem_edgeSet.mpr hrem⟩
          have hemb : embeddedEdgeEmbedding (sourceMarkedRawCentralGraph a w h u v A)
              (rectangleGraph a w h) (pocketInclusion S)
              (sourceMarkedRawCentralGraph_map_le_original a w h u v A) d = e := by
            apply Subtype.ext
            exact hev.symm
          rw [embeddedConfigurationEmbedding_eq_map]
          apply Finset.mem_map.mpr
          refine ⟨d,?_,hemb⟩
          exact (mem_embeddedConfigurationRestriction _ _ _ _ B d).mpr (hemb ▸ heB)
        · exact Finset.mem_union_left _ he }
  refine ⟨(p.induce S hs).map f,?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  rw [p.support_induce hs,List.mem_attachWith] at hy
  exact hp y.val hy

end
end PottsContinuity.Thm3.Prop4
