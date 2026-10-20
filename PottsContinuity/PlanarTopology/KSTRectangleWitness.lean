module

public import PottsContinuity.PlanarTopology.KSTSideBridge
public import PottsContinuity.PD.Duality.RectangleWalks
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Actual open walks in a sampled rectangle restriction use only original
whole-plane open bonds after forgetting the rectangle subtype. -/
theorem kstPathOpen_of_rectangle_walk (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h)
      (embeddedRestriction _ (frozenEdgeEmbedding (latticeRectangle a w h)) ω)).Walk u v) :
    kstPathOpen ω (p.map (rectangleOpenGraphToSquare a w h _)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f,hf,hfe⟩ := List.mem_map.mp he
  have hopen := p.edges_subset_edgeSet hf
  rw [openGraph_edgeSet] at hopen
  obtain ⟨g,hg,hgf⟩ := hopen
  have hgO : ω (frozenEdgeEmbedding (latticeRectangle a w h) g) = true :=
    (mem_embeddedRestriction _ _ _ g).mp hg
  have heq : frozenEdgeEmbedding (latticeRectangle a w h) g = e := by
    apply Subtype.ext
    change Sym2.map (fun z : RectangleVertex a w h => z.val) g.val = e.val
    rw [hgf]
    exact hfe
  rwa [heq] at hgO

/-- A horizontal rectangle event provides a simple original lattice walk,
with exact side endpoints, original open edges and literal support bounds. -/
theorem kst_horizontal_crossing_witness (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ horizontalRectangle a w h) :
    ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
      p.IsPath ∧ kstPathOpen ω p ∧ u.1 = a.1 ∧ v.1 = a.1+(w : ℤ) ∧
      kstPathIn p a.1 (a.1+(w : ℤ)) a.2 (a.2+(h : ℤ)) := by
  obtain ⟨u,v,hu,hv,hconn⟩ := hω
  obtain ⟨p,hp⟩ := hconn.exists_isPath
  refine ⟨u.val,v.val,p.map (rectangleOpenGraphToSquare _ _ _ _),
    hp.map Subtype.val_injective,kstPathOpen_of_rectangle_walk a w h ω p,
    (Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,?_⟩
  intro z hz
  obtain ⟨z',_,he⟩ := rectangleOpenWalk_mapped_support_preimage a w h _ p hz
  rw [← he]
  have hh := (mem_latticeRectangle a z'.val w h).mp z'.property
  exact ⟨hh.1.1,hh.1.2,hh.2⟩

end
end PottsContinuity.PlanarTopology
