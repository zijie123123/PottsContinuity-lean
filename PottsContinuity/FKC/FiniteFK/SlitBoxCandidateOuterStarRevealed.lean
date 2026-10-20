-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateOuterStarRevealed.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateRightStrip
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateHorizontalStrips
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateOffPathStar
public import PottsContinuity.FKC.FiniteFK.SlitBoxCellIncidentStar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Domains
open PottsContinuity.FKC.Medial
open PottsContinuity.FKC.LatticePolygon

/-- At an actual candidate vertex off both its original path and the wired
arc, reveal status of an incident slit edge is exactly membership of the
vertex's northeast cell in the actual polygon filling. -/
theorem slitBoxCandidate_off_path_arc_incident_edge_mem_iff_cell_mem
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hvPath : v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : v ∉ slitBoxWiredArc n)
    (e : (slitBoxGraph n).edgeSet) (hincident : v ∈ e.val) :
    e ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) ↔
      v.val ∈ (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ := by
  let c := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let F := P.interiorCellBases δ
  have hv : v.val ∉ c.support :=
    slitBoxFirstHitCandidateCycle_off_path_arc_not_mem_support
      n hn u huY huX p v hvPath hvArc
  have hc : c.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  have hboundary : latticeCellBoundaryGraph F = c.toSubgraph.spanningCoe := by
    simpa [F, P, c, slitBoxFirstHitCandidatePolygon,
      slitBoxFirstHitCandidateCycle] using
        latticeCellBoundaryGraph_interiorCellBases_eq_cycle hc δ
  have hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v.val w := by
    intro w hadj
    have hEdge : s(v.val, w) ∈ (latticeCellBoundaryGraph F).edgeSet :=
      (latticeCellBoundaryGraph F).mem_edgeSet.mpr hadj
    rw [hboundary] at hEdge
    have hwalkEdge : s(v.val, w) ∈ c.edges := by
      have hiff : s(v.val, w) ∈ (c.toSubgraph.spanningCoe).edgeSet ↔
          s(v.val, w) ∈ c.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hEdge
    exact hv (c.fst_mem_support_of_mem_edges hwalkEdge)
  rw [slitBoxCellIncidentEdges_iff_vertex_mem n F v hNo e hincident]

/-- On the right side or the nonnegative top side of a genuine candidate,
every actual incident slit edge belongs to the incident-edge reveal of its
actual filling, provided the vertex is off the path and wired arc. -/
theorem slitBoxFirstHitCandidate_outer_star_incident_edges_revealed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hvPath : v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : v ∉ slitBoxWiredArc n)
    (hside : v.val.1 = n ∨ (v.val.2 = n ∧ 0 ≤ v.val.1))
    (e : (slitBoxGraph n).edgeSet) (hincident : v ∈ e.val) :
    e ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
  apply (slitBoxCandidate_off_path_arc_incident_edge_mem_iff_cell_mem
    n hn u huY huX δ p v hvPath hvArc e hincident).2
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  rcases hside with hright | ⟨htop, hleft⟩
  · have hvbox := v.property
    rw [mem_latticeRectangle] at hvbox
    have htopCoord : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
      push_cast
      omega
    rw [htopCoord] at hvbox
    have hlo : -(n + 1 : ℤ) ≤ v.val.2 := by omega
    have hhi : v.val.2 ≤ (n : ℤ) := hvbox.2.2
    have hcenter : latticeCellCenter δ ((n : ℤ), v.val.2) ∈ P.domain δ := by
      simpa [P] using slitBoxFirstHitCandidate_right_strip_inside
        n hn u huY huX δ p v.val.2 hlo hhi
    have hcell := (P.mem_interiorCellBases_iff δ ((n : ℤ), v.val.2)).2 hcenter
    have hcoords : ((n : ℤ), v.val.2) = v.val := by
      ext <;> simp [hright]
    rw [hcoords] at hcell
    exact hcell
  · have hvbox := v.property
    rw [mem_latticeRectangle] at hvbox
    have htopCoord : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
      push_cast
      omega
    rw [htopCoord] at hvbox
    have hlo : 0 ≤ v.val.1 := hleft
    have hhi : v.val.1 ≤ (n : ℤ) := hvbox.1.2
    have hcenter : latticeCellCenter δ (v.val.1, (n : ℤ)) ∈ P.domain δ := by
      simpa [P] using slitBoxFirstHitCandidate_top_strip_inside
        n hn u huY huX δ p v.val.1 hlo hhi
    have hcell := (P.mem_interiorCellBases_iff δ (v.val.1, (n : ℤ))).2 hcenter
    have hcoords : (v.val.1, (n : ℤ)) = v.val := by
      ext <;> simp [htop]
    rw [hcoords] at hcell
    exact hcell

end PottsContinuity.FKC.FiniteFK
