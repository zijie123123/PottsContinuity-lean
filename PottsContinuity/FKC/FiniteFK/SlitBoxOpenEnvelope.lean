-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxOpenEnvelope.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionCycleFilling
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionCycleUnion
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxIntersectionCycleCandidate
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Domains

/-- Two actual open first-hit candidates have an actual first-hit candidate
whose actual polygon filling is contained in their intersection and whose
retained-path support is covered by theirs. -/
theorem slitBoxFirstHitCandidate_exists_open_envelope
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (A : Configuration (slitBoxGraph n))
    (hpOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A)
    (hqOpen : slitBoxCandidateOriginalPathEdgeSupport n u q ⊆ A) :
    ∃ r : SlitBoxFirstHitBaseCandidates n u,
      (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ ⊆
          (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
            (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ ∧
      slitBoxCandidateOriginalPathEdgeSupport n u r ⊆
        slitBoxCandidateOriginalPathEdgeSupport n u p ∪
          slitBoxCandidateOriginalPathEdgeSupport n u q ∧
      slitBoxCandidateOriginalPathEdgeSupport n u r ⊆ A := by
  classical
  let F :=
    (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
      (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
  obtain ⟨z, c, hc, hright, hboundary, hcfill⟩ :=
    slitBoxFirstHitCandidateIntersection_right_cycle_filling_subset
      n hn u huY huX δ p q
  obtain ⟨r, hsame⟩ :=
    slitBoxFirstHitIntersectionCycle_actual_candidate_reconstruction
      n hn u huY huX δ p q c hc hright (by simpa [F] using hboundary)
  have hcycleR : (slitBoxFirstHitCandidateCycle n hn u huY huX r).IsCycle :=
    slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX r
  have hcomplement : (squareLattice.induce {x : LatticeVertex | x ∉ F}).Connected := by
    simpa [F, slitBoxFirstHitCandidatePolygon] using
      squareLattice_induce_compl_inter_cycleInteriorBases_connected
        (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p)
        (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX q) δ
  have hboundaryR : ∀ e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX r).edges,
      e ∈ (latticeCellBoundaryGraph F).edgeSet := by
    intro e he
    exact hboundary e ((hsame e).mp he)
  have hfillR :
      (slitBoxFirstHitCandidatePolygon n hn u huY huX r).interiorCellBases δ ⊆ F := by
    simpa [slitBoxFirstHitCandidatePolygon] using
      latticePolygonOfCycle_interiorCellBases_subset_of_cycle_edges_in_boundary
        hcycleR δ F hcomplement hboundaryR
  have hsupportUnion :
      slitBoxCandidateOriginalPathEdgeSupport n u r ⊆
        slitBoxCandidateOriginalPathEdgeSupport n u p ∪
          slitBoxCandidateOriginalPathEdgeSupport n u q := by
    intro e he
    have hePath :=
      (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u r e).mp he
    have heR :=
      (slitBoxFirstHitCandidateCycle_slitEdge_mem_iff n hn u huY huX r e).2 hePath
    have heC := (hsame (Sym2.map Subtype.val e.val)).mp heR
    have hpq := slitBoxFirstHitCandidateIntersection_cycle_edges_subset_union
      n hn u huY huX δ p q c hc (by simpa [F] using hboundary)
      (Sym2.map Subtype.val e.val) heC
    rcases hpq with hp | hq
    · exact Finset.mem_union.mpr (Or.inl
        ((mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p e).2
          ((slitBoxFirstHitCandidateCycle_slitEdge_mem_iff n hn u huY huX p e).mp hp)))
    · exact Finset.mem_union.mpr (Or.inr
        ((mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u q e).2
          ((slitBoxFirstHitCandidateCycle_slitEdge_mem_iff n hn u huY huX q e).mp hq)))
  have hopenR : slitBoxCandidateOriginalPathEdgeSupport n u r ⊆ A := by
    intro e he
    rcases Finset.mem_union.mp (hsupportUnion he) with hp | hq
    · exact hpOpen hp
    · exact hqOpen hq
  exact ⟨r, by simpa [F] using hfillR, hsupportUnion, hopenR⟩

end PottsContinuity.FKC.FiniteFK

