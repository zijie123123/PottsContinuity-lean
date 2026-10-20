-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxBottomCenterUnrevealed.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateOffPathStar
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBottomExteriorCell
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryVertexStar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Domains
open PottsContinuity.FKC.LatticePolygon

/-- Every actual slit-graph edge incident to the bottom-center vertex is
unrevealed by the actual filling of a right-side candidate whose path avoids
that vertex. -/
theorem slitBoxBottomCenter_all_incident_edges_unrevealed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (hcenterPath : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support) :
    ∀ e : (slitBoxGraph n).edgeSet,
      slitBoxBottomCenterVertex n ∈ e.val →
      e ∉ slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY (le_of_lt huX) p).interiorCellBases δ) := by
  classical
  let v := slitBoxBottomCenterVertex n
  let P := slitBoxFirstHitCandidatePolygon n hn u huY (le_of_lt huX) p
  let c := slitBoxFirstHitCandidateCycle n hn u huY (le_of_lt huX) p
  let F := P.interiorCellBases δ
  have hvArc : v ∉ slitBoxWiredArc n := slitBoxBottomCenterVertex_off_arc n hn
  have hvCycle : v.val ∉ c.support := by
    simpa [v, c] using slitBoxFirstHitCandidateCycle_off_path_arc_not_mem_support
      n hn u huY (le_of_lt huX) p v hcenterPath hvArc
  have hstar := latticePolygonCycle_off_support_four_cells_agree
    (slitBoxFirstHitCandidateCycle_isCycle n hn u huY (le_of_lt huX) p) δ
    v.val hvCycle
  have hbottom : (0, -(n + 1 : ℤ)) ∉ F := by
    simpa [F, P, slitBoxFirstHitCandidatePolygon] using
      slitBoxFirstHitCandidate_bottom_exterior_cell n hn u huY huX δ p
  have hcenterNot : v.val ∉ F := by
    intro hv
    apply hbottom
    have hsouth := hstar.2.1.mp hv
    change (v.val.1, v.val.2 - 1) ∈ F at hsouth
    have heq : (v.val.1, v.val.2 - 1) = (0, -(n + 1 : ℤ)) := by
      change ((slitBoxBottomCenterVertex n).val.1,
        (slitBoxBottomCenterVertex n).val.2 - 1) = (0, -(n + 1 : ℤ))
      rw [slitBoxBottomCenterVertex_val]
      apply Prod.ext <;> simp; omega
    rw [← heq]
    exact hsouth
  have hboundaryGraph : latticeCellBoundaryGraph F = c.toSubgraph.spanningCoe := by
    simpa [F, P, c, slitBoxFirstHitCandidatePolygon, slitBoxFirstHitCandidateCycle] using
      latticeCellBoundaryGraph_interiorCellBases_eq_cycle
        (slitBoxFirstHitCandidateCycle_isCycle n hn u huY (le_of_lt huX) p) δ
  have hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v.val w := by
    intro w hadj
    have hedge : s(v.val,w) ∈ (latticeCellBoundaryGraph F).edgeSet :=
      (latticeCellBoundaryGraph F).mem_edgeSet.mpr hadj
    rw [hboundaryGraph] at hedge
    have hwalkEdge : s(v.val,w) ∈ c.edges := by
      have hiff : s(v.val,w) ∈ (c.toSubgraph.spanningCoe).edgeSet ↔
          s(v.val,w) ∈ c.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hedge
    exact hvCycle (c.fst_mem_support_of_mem_edges hwalkEdge)
  intro e he
  have hiff := slitBoxCellIncidentEdges_iff_vertex_mem n F v hNo e he
  intro hrevealed
  exact hcenterNot (hiff.mp hrevealed)

/-- For `n ≥ 1`, the bottom-center vertex has a concrete retained upward edge;
combined with the preceding theorem this gives a nonempty actual unrevealed
incident star. -/
theorem slitBoxBottomCenter_has_unrevealed_upward_edge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (hcenterPath : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support) :
    ∃ e : (slitBoxGraph n).edgeSet,
      slitBoxBottomCenterVertex n ∈ e.val ∧
      e ∉ slitBoxCellIncidentEdges n
        ((slitBoxFirstHitCandidatePolygon n hn u huY (le_of_lt huX) p).interiorCellBases δ) := by
  let v := slitBoxBottomCenterVertex n
  let w : SlitBoxVertex n := ⟨(0, -(n : ℤ) + 1), by
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · constructor <;> omega⟩
  have hadjSquare : squareLattice.Adj v.val w.val := by
    rw [slitBoxBottomCenterVertex_val]
    change squareLattice.Adj (0, -(n : ℤ)) (0, -(n : ℤ) + 1)
    rw [squareLattice_adj_iff]
    exact Or.inr ⟨rfl, Or.inl rfl⟩
  have hvArc : v ∉ slitBoxWiredArc n := slitBoxBottomCenterVertex_off_arc n hn
  have hnotBoth : ¬ (v ∈ slitBoxWiredArc n ∧ w ∈ slitBoxWiredArc n) := by
    intro h
    exact hvArc h.1
  have hnotBothCoord : ¬
      ((v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n) ∧
       (w.val.1 = 0 ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ n)) := by
    simpa only [mem_slitBoxWiredArc_iff] using hnotBoth
  have hadj : (slitBoxGraph n).Adj v w :=
    (slitBoxGraph_adj_iff n v w).2 ⟨hadjSquare, hnotBothCoord⟩
  let e : (slitBoxGraph n).edgeSet := ⟨s(v,w), (slitBoxGraph n).mem_edgeSet.mpr hadj⟩
  have hincident : slitBoxBottomCenterVertex n ∈ e.val := by
    change v ∈ s(v,w)
    exact (Sym2.mem_iff').2 (Or.inl rfl)
  exact ⟨e, hincident,
    slitBoxBottomCenter_all_incident_edges_unrevealed n hn u huY huX δ p hcenterPath e hincident⟩

end PottsContinuity.FKC.FiniteFK
