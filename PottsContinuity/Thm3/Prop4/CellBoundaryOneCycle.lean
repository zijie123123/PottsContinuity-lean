module

public import PottsContinuity.Thm3.Prop4.CellRegionIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # A connected cell region with connected exterior has one boundary cycle -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

/-- Every traversed bond of a cell-boundary walk really separates the two
cell labels; normalized bond identity retains the original crossed edge. -/
theorem cell_boundary_walk_bond_separates (S : Finset LatticeVertex)
    {u v : LatticeVertex} (p : (latticeCellBoundaryGraph S).Walk u v)
    (b : LatticeBond) (hb : b.toSym2 ∈ (p.mapLe (latticeCellBoundaryGraph_le S)).edges) :
    (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S) := by
  have he : b.toSym2 ∈ p.edges := by
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using hb
  have hed := p.edges_subset_edgeSet he
  have hadj : (latticeCellBoundaryGraph S).Adj b.source b.target :=
    (latticeCellBoundaryGraph S).mem_edgeSet.mp hed
  obtain ⟨_,c,hcb,hlabels⟩ := (latticeCellBoundaryGraph_adj_iff S _ _).mp hadj
  have hcb' : c = b := LatticeBond.toSym2_injective hcb
  subst c
  exact Ne.symm hlabels

/-- If both face labels give connected regions, every boundary edge belongs
to one simple cycle. This excludes additional hole boundaries within that region. -/
theorem cell_boundary_one_cycle_of_regions_connected (S : Finset LatticeVertex)
    (hinside : (squareLattice.induce (S : Set LatticeVertex)).Preconnected)
    (houtside : (squareLattice.induce (S : Set LatticeVertex)ᶜ).Preconnected)
    {u v : LatticeVertex} (huv : (latticeCellBoundaryGraph S).Adj u v) :
    ∃ z : LatticeVertex, ∃ p : (latticeCellBoundaryGraph S).Walk z z,
      p.IsCycle ∧ ∀ b : LatticeBond,
        (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S) → b.toSym2 ∈ p.edges := by
  classical
  obtain ⟨z,p,hp,huvP⟩ := edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet
    (latticeCellBoundaryGraph S) (latticeCellBoundaryGraph_edgeSet_finite S)
    (latticeCellBoundaryGraph_even_degree S) huv
  let q := p.mapLe (latticeCellBoundaryGraph_le S)
  have supportLabels := cell_boundary_walk_bond_separates S p
  have const (x y : LatticeVertex) (hlabel : (x ∈ S) = (y ∈ S)) :
      rayIndex (faceIndexMark x) q = rayIndex (faceIndexMark y) q := by
    by_cases hx : x ∈ S
    · have hy : y ∈ S := hlabel ▸ hx
      exact cell_boundary_constant_region_index_eq S q supportLabels (S : Set LatticeVertex)
        (fun a b => propext (iff_of_true a.property b.property))
        (hinside ⟨x,hx⟩ ⟨y,hy⟩)
    · have hy : y ∉ S := hlabel ▸ hx
      exact cell_boundary_constant_region_index_eq S q supportLabels (S : Set LatticeVertex)ᶜ
        (fun a b => propext (iff_of_false a.property b.property))
        (houtside ⟨x,hx⟩ ⟨y,hy⟩)
  obtain ⟨_,b,hb,hbDiff⟩ := (latticeCellBoundaryGraph_adj_iff S _ _).mp huv
  have hbq : b.toSym2 ∈ q.edges := by
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges,hb]
    exact huvP
  have hnodup : q.edges.Nodup := by
    dsimp only [q]
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact hp.isTrail.edges_nodup
  have hbIdx := rayIndex_bond_faces_ne_of_mem q hnodup b hbq
  have xorLabel (b : LatticeBond)
      (h : (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S)) :
      (b.faceBase true ∈ S ↔ b.faceBase false ∉ S) := by
    by_cases hf : b.faceBase false ∈ S
    · have ht : b.faceBase true ∉ S := by
        intro ht
        exact h (propext (iff_of_true hf ht))
      simp only [hf,ht,not_true_eq_false,iff_self]
    · have ht : b.faceBase true ∈ S := by
        by_contra ht
        exact h (propext (iff_of_false hf ht))
      simp only [hf,ht,not_false_eq_true,iff_self]
  have hbX := xorLabel b (Ne.symm hbDiff)
  refine ⟨z,p,hp,?_⟩
  intro c hcDiff
  have hcX := xorLabel c hcDiff
  by_contra hcP
  have hcQ : c.toSym2 ∉ q.edges := by
    simpa only [q,SimpleGraph.Walk.edges_mapLe_eq_edges] using hcP
  have hcIdx := rayIndex_bond_faces_eq_of_not_mem q c hcQ
  by_cases hb0 : b.faceBase false ∈ S <;> by_cases hc0 : c.faceBase false ∈ S
  · have hb1' : b.faceBase true ∉ S := fun h => (hbX.mp h) hb0
    have hc1' : c.faceBase true ∉ S := fun h => (hcX.mp h) hc0
    exact hbIdx ((const _ _ (propext (iff_of_true hb0 hc0))).trans
      (hcIdx.trans (const _ _ (propext (iff_of_false hc1' hb1')))))
  · have hb1 : b.faceBase true ∉ S := fun h => (hbX.mp h) hb0
    have hc1 : c.faceBase true ∈ S := hcX.mpr hc0
    exact hbIdx ((const _ _ (propext (iff_of_true hb0 hc1))).trans
      (hcIdx.symm.trans (const _ _ (propext (iff_of_false hc0 hb1)))))
  · have hb1 : b.faceBase true ∈ S := hbX.mpr hb0
    have hc1 : c.faceBase true ∉ S := fun h => (hcX.mp h) hc0
    exact hbIdx ((const _ _ (propext (iff_of_false hb0 hc1))).trans
      (hcIdx.symm.trans (const _ _ (propext (iff_of_true hc0 hb1)))))
  · have hb1 : b.faceBase true ∈ S := hbX.mpr hb0
    have hc1 : c.faceBase true ∈ S := hcX.mpr hc0
    exact hbIdx ((const _ _ (propext (iff_of_false hb0 hc0))).trans
      (hcIdx.trans (const _ _ (propext (iff_of_true hc1 hb1)))))

/-- All endpoints of the actual boundary bonds lie in one actual boundary
component, when the cell region and its exterior are connected. -/
theorem cell_boundary_bond_vertices_connected (S : Finset LatticeVertex)
    (hinside : (squareLattice.induce (S : Set LatticeVertex)).Preconnected)
    (houtside : (squareLattice.induce (S : Set LatticeVertex)ᶜ).Preconnected)
    (b c : LatticeBond)
    (hb : (b.faceBase false ∈ S) ≠ (b.faceBase true ∈ S))
    (hc : (c.faceBase false ∈ S) ≠ (c.faceBase true ∈ S))
    (x y : LatticeVertex) (hx : x ∈ b.toSym2) (hy : y ∈ c.toSym2) :
    (latticeCellBoundaryGraph S).Reachable x y := by
  have hbadj : (latticeCellBoundaryGraph S).Adj b.source b.target := by
    apply (latticeCellBoundaryGraph_adj_iff S _ _).mpr
    refine ⟨?_,b,rfl,Ne.symm hb⟩
    rcases b with ⟨⟨a,d⟩,axis⟩
    cases axis <;> simp [squareLattice_adj_iff,LatticeBond.source,LatticeBond.target]
  obtain ⟨z,p,hp,hedges⟩ := cell_boundary_one_cycle_of_regions_connected S hinside houtside hbadj
  have hxp := SimpleGraph.Walk.mem_support_of_mem_edges (hedges b hb) hx
  have hyp := SimpleGraph.Walk.mem_support_of_mem_edges (hedges c hc) hy
  exact (p.takeUntil x hxp).reachable.symm.trans (p.takeUntil y hyp).reachable

end
end PottsContinuity.Thm3.Prop4
