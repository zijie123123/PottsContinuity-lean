-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateIntersectionCycleFilling.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionCycle
public import PottsContinuity.FKC.Domains.LatticeCellIntersectionExteriorConnectivity
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryOrder
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryGraphFaithfulness
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Domains
open PottsContinuity.FKC.LatticePolygon
open SimpleGraph

/-- If every edge of a genuine square-lattice cycle lies in the actual cell
boundary graph of `F`, then the cycle's actual polygon filling is contained in
`F`, provided the induced complement of `F` is connected. -/
theorem latticePolygonOfCycle_interiorCellBases_subset_of_cycle_edges_in_boundary
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (δ : PositiveMesh) (F : Finset LatticeVertex)
    (hcomplement : (squareLattice.induce
      {z : LatticeVertex | z ∉ F}).Connected)
    (hedges : ∀ e ∈ p.edges, e ∈ (latticeCellBoundaryGraph F).edgeSet) :
    (latticePolygonOfCycle hp).interiorCellBases δ ⊆ F := by
  classical
  let S := (latticePolygonOfCycle hp).interiorCellBases δ
  have hcycle : latticeCellBoundaryGraph S = p.toSubgraph.spanningCoe := by
    simpa [S] using latticeCellBoundaryGraph_interiorCellBases_eq_cycle hp δ
  have hedgesGraph : latticeCellBoundaryGraph S ≤ latticeCellBoundaryGraph F := by
    intro a b hab
    have hedgeS : s(a,b) ∈ (latticeCellBoundaryGraph S).edgeSet :=
      (latticeCellBoundaryGraph S).mem_edgeSet.mpr hab
    rw [hcycle] at hedgeS
    have hcycleEdges : s(a,b) ∈ p.edges := by
      have hiff : s(a,b) ∈ (p.toSubgraph.spanningCoe).edgeSet ↔ s(a,b) ∈ p.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hedgeS
    exact (latticeCellBoundaryGraph F).mem_edgeSet.mp (hedges _ hcycleEdges)
  have hboundary : latticeCellBoundaryBonds S ⊆ latticeCellBoundaryBonds F :=
    (latticeCellBoundaryGraph_le_iff S F).mp hedgesGraph
  have hsubset : S ⊆ F :=
    latticeCellBoundaryBonds_subset_of_complement_connected S F hcomplement hboundary
  simpa [S] using hsubset

/-- The actual cycle extracted from the intersection boundary through the
common right edge has its actual polygon filling inside the actual candidate
intersection. -/
theorem slitBoxFirstHitCandidateIntersection_right_cycle_filling_subset
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u) :
    let F :=
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
        (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
    ∃ (z : LatticeVertex) (c : squareLattice.Walk z z),
      ∃ hc : c.IsCycle,
      s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges ∧
      (∀ e ∈ c.edges, e ∈ (latticeCellBoundaryGraph F).edgeSet) ∧
      (latticePolygonOfCycle hc).interiorCellBases δ ⊆ F := by
  classical
  let F :=
    (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
      (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
  obtain ⟨z,c,hcycle,hright,hedges⟩ :=
    slitBoxFirstHitCandidateIntersection_right_cycle n hn u huY huX δ p q
  have hcomplement : (squareLattice.induce
      {x : LatticeVertex | x ∉ F}).Connected := by
    simpa [F, slitBoxFirstHitCandidatePolygon] using squareLattice_induce_compl_inter_cycleInteriorBases_connected
      (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p)
      (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX q) δ
  have hfill := latticePolygonOfCycle_interiorCellBases_subset_of_cycle_edges_in_boundary
    hcycle δ F hcomplement hedges
  exact ⟨z,c,hcycle,hright,by simpa [F] using hedges,
    by simpa [F] using hfill⟩

end PottsContinuity.FKC.FiniteFK
