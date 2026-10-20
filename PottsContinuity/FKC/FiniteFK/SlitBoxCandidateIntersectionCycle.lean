-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateIntersectionCycle.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionRightBoundary
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryParity
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryFiniteEdges
public import PottsContinuity.FKC.FiniteFK.FiniteSupportEvenEdgeCycle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The actual intersection boundary contains a genuine square-lattice cycle
through the common right-side bond. Every edge of the cycle remains in the
actual boundary graph of the intersection. -/
theorem slitBoxFirstHitCandidateIntersection_right_cycle
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u) :
    let F :=
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
        (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
    ∃ (z : LatticeVertex) (c : squareLattice.Walk z z),
      c.IsCycle ∧
      s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges ∧
      ∀ e ∈ c.edges, e ∈ (latticeCellBoundaryGraph F).edgeSet := by
  classical
  let F :=
    (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
      (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
  let G := latticeCellBoundaryGraph F
  have hadj : G.Adj ((n + 1 : ℤ), 0) ((n + 1 : ℤ), 1) := by
    simpa [F] using slitBoxFirstHitCandidateIntersection_right_boundaryGraph_adj
      n hn u huY huX δ p q 0 (by omega) (by omega)
  obtain ⟨z, c, hc, hbond⟩ :=
    edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet G
      (latticeCellBoundaryGraph_edgeSet_finite F)
      (latticeCellBoundaryGraph_even_degree F) hadj
  let f : G →g squareLattice :=
    { toFun := id, map_rel' := by
        intro a b hab
        exact latticeCellBoundaryGraph_le F hab }
  let c' := c.map f
  have hc' : c'.IsCycle :=
    (c.isCycle_map_iff_of_injective (by intro a b h; exact h)).mpr hc
  have hbond' : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c'.edges := by
    have hmap : c'.edges = c.edges.map (Sym2.map f) := by
      change (c.map f).edges = c.edges.map (Sym2.map f)
      rw [SimpleGraph.Walk.edges_map]
    rw [hmap]
    exact List.mem_map.mpr ⟨s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)), hbond, by
      simp [f]⟩
  have hsubset : ∀ e ∈ c'.edges, e ∈ G.edgeSet := by
    intro e he
    have hmap : c'.edges = c.edges.map (Sym2.map f) := by
      change (c.map f).edges = c.edges.map (Sym2.map f)
      rw [SimpleGraph.Walk.edges_map]
    rw [hmap] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    have heG : e₀ ∈ G.edgeSet := c.edges_subset_edgeSet he₀
    simpa [f] using heG
  exact ⟨z, c', hc', hbond', hsubset⟩

end PottsContinuity.FKC.FiniteFK
