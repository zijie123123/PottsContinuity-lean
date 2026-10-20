module

public import PottsContinuity.Thm3.Push.ActiveFrontierComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Deleting the recorded original bonds commutes with literal graph
inclusion as a subgraph relation. All outer unrecorded bonds remain present. -/
theorem edgeRestriction_map_le_embedded {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (R : Configuration G) :
    (edgeRestriction G R).map f ≤
      edgeRestriction H (R.map (embeddedEdgeEmbedding G H f hGH)) := by
  classical
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  have hGxy := edgeRestriction_le G R hxy
  have hHxy : H.Adj (f x) (f y) :=
    hGH ((SimpleGraph.map_adj _ _ _ _).mpr ⟨x,y,hGxy,rfl,rfl⟩)
  let e : G.edgeSet := ⟨s(x,y),G.mem_edgeSet.mpr hGxy⟩
  let g := embeddedEdgeEmbedding G H f hGH e
  have hge : g.val=s(f x,f y) := rfl
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hHxy,?_⟩
  intro hmem
  have hg : g ∈ R.map (embeddedEdgeEmbedding G H f hGH) :=
    (coe_mem_openEdges_iff _ _ g).mp (hge.symm ▸ hmem)
  have he : e ∈ R := (Finset.mem_map' _).mp hg
  exact (SimpleGraph.deleteEdges_adj.mp hxy).2 ((coe_mem_openEdges_iff G R e).mpr he)

/-- Actual active reference bonds embed into the outer remaining graph.
The carrier includes no virtual edges and retains the outer exterior. -/
theorem activeUnexaminedGraph_map_le_outer_remaining {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (R : Configuration G) :
    (activeUnexaminedGraph G R).map ((Function.Embedding.subtype _).trans f) ≤
      edgeRestriction H (R.map (embeddedEdgeEmbedding G H f hGH)) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  apply edgeRestriction_map_le_embedded G H f hGH R
  exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨x.val,y.val,hxy,rfl,rfl⟩

end
end PottsContinuity.Push
