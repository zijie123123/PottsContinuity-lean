-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateIntersectionCycleUnion.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionRightBoundary
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryGraphFaithfulness
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.LatticePolygon
open SimpleGraph

/-- The actual cell-boundary graph of the candidate-interior intersection is
contained in the union of the two actual candidate-cycle graphs. -/
theorem slitBoxFirstHitCandidateIntersection_boundaryGraph_le_cycleSup
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u) :
    let Pp := slitBoxFirstHitCandidatePolygon n hn u huY huX p
    let Pq := slitBoxFirstHitCandidatePolygon n hn u huY huX q
    let F := Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ
    latticeCellBoundaryGraph F ≤
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).toSubgraph.spanningCoe ⊔
        (slitBoxFirstHitCandidateCycle n hn u huY huX q).toSubgraph.spanningCoe := by
  classical
  let Pp := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let Pq := slitBoxFirstHitCandidatePolygon n hn u huY huX q
  let F := Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  have hpGraph : latticeCellBoundaryGraph (Pp.interiorCellBases δ) =
      cp.toSubgraph.spanningCoe := by
    simpa [Pp, cp, slitBoxFirstHitCandidatePolygon] using
      latticeCellBoundaryGraph_interiorCellBases_eq_cycle
        (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p) δ
  have hqGraph : latticeCellBoundaryGraph (Pq.interiorCellBases δ) =
      cq.toSubgraph.spanningCoe := by
    simpa [Pq, cq, slitBoxFirstHitCandidatePolygon] using
      latticeCellBoundaryGraph_interiorCellBases_eq_cycle
        (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX q) δ
  rw [SimpleGraph.le_iff_adj]
  intro a b hab
  obtain ⟨hadj, e, heq, hfaces⟩ :=
    (latticeCellBoundaryGraph_adj_iff F a b).mp hab
  have heF : e ∈ latticeCellBoundaryBonds F :=
    (mem_latticeCellBoundaryBonds F e).mpr hfaces
  have heUnion : e ∈ latticeCellBoundaryBonds (Pp.interiorCellBases δ) ∪
      latticeCellBoundaryBonds (Pq.interiorCellBases δ) := by
    have h := latticeCellBoundaryBonds_inter_subset_union
      (Pp.interiorCellBases δ) (Pq.interiorCellBases δ) heF
    simpa [F] using h
  rcases Finset.mem_union.mp heUnion with heP | heQ
  · have hPfaces := (mem_latticeCellBoundaryBonds (Pp.interiorCellBases δ) e).mp heP
    have hPAdj : (latticeCellBoundaryGraph (Pp.interiorCellBases δ)).Adj a b :=
      (latticeCellBoundaryGraph_adj_iff _ a b).2 ⟨hadj, e, heq, hPfaces⟩
    rw [hpGraph] at hPAdj
    exact SimpleGraph.sup_adj _ _ _ _ |>.2 (Or.inl hPAdj)
  · have hQfaces := (mem_latticeCellBoundaryBonds (Pq.interiorCellBases δ) e).mp heQ
    have hQAdj : (latticeCellBoundaryGraph (Pq.interiorCellBases δ)).Adj a b :=
      (latticeCellBoundaryGraph_adj_iff _ a b).2 ⟨hadj, e, heq, hQfaces⟩
    rw [hqGraph] at hQAdj
    exact SimpleGraph.sup_adj _ _ _ _ |>.2 (Or.inr hQAdj)

private theorem walkEdge_mem_spanningCycle_iff
    {z : LatticeVertex} (c : squareLattice.Walk z z) (e : Sym2 LatticeVertex) :
    e ∈ c.toSubgraph.spanningCoe.edgeSet ↔ e ∈ c.edges := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
  rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
    SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]

/-- Every edge of a genuine cycle lying in the actual intersection boundary
belongs to one of the two actual candidate-cycle edge lists. -/
theorem slitBoxFirstHitCandidateIntersection_cycle_edges_subset_union
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex} (c : squareLattice.Walk z z) (_hc : c.IsCycle)
    (hedges : ∀ e ∈ c.edges,
      e ∈ (latticeCellBoundaryGraph
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) :
    ∀ e ∈ c.edges,
      e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges ∨
        e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges := by
  classical
  let Pp := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let Pq := slitBoxFirstHitCandidatePolygon n hn u huY huX q
  let F := Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  have hsub : latticeCellBoundaryGraph F ≤ cp.toSubgraph.spanningCoe ⊔
      cq.toSubgraph.spanningCoe := by
    simpa [Pp, Pq, F, cp, cq] using
      slitBoxFirstHitCandidateIntersection_boundaryGraph_le_cycleSup
        n hn u huY huX δ p q
  intro e he
  have heF : e ∈ (latticeCellBoundaryGraph F).edgeSet := by
    simpa [F] using hedges e he
  have heSup : e ∈ (cp.toSubgraph.spanningCoe ⊔ cq.toSubgraph.spanningCoe).edgeSet :=
    SimpleGraph.edgeSet_mono hsub heF
  rw [SimpleGraph.edgeSet_sup] at heSup
  simp only [Set.mem_union] at heSup
  rcases heSup with heP | heQ
  · exact Or.inl ((walkEdge_mem_spanningCycle_iff cp e).mp heP)
  · exact Or.inr ((walkEdge_mem_spanningCycle_iff cq e).mp heQ)

end PottsContinuity.FKC.FiniteFK
