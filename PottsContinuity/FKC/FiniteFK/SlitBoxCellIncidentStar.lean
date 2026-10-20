-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCellIncidentStar.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCellIncidentEdges
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryVertexStar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open PottsContinuity.FKC.Domains
open PottsContinuity.FKC.LatticePolygon

private theorem incidentBond_eq_one_of_four
    (v : LatticeVertex) (b : LatticeBond)
    (hinc : v = b.source ∨ v = b.target) :
    b = ⟨v, LatticeAxis.horizontal⟩ ∨
      b = ⟨v, LatticeAxis.vertical⟩ ∨
      b = ⟨(v.1 - 1, v.2), LatticeAxis.horizontal⟩ ∨
      b = ⟨(v.1, v.2 - 1), LatticeAxis.vertical⟩ := by
  rcases v with ⟨vx, vy⟩
  rcases b with ⟨⟨x, y⟩, axis⟩
  cases axis
  · simp only [LatticeBond.source, LatticeBond.target] at hinc
    rcases hinc with h | h
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact Or.inl rfl
    · rcases Prod.mk.inj h with ⟨hx, hy⟩
      have hx' : x = vx - 1 := by omega
      subst x
      subst y
      exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [LatticeBond.source, LatticeBond.target] at hinc
    rcases hinc with h | h
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl rfl)
    · rcases Prod.mk.inj h with ⟨hx, hy⟩
      have hy' : y = vy - 1 := by omega
      subst x
      subst y
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem slitEdge_endpoint_data (n : ℕ)
    (f : Sym2 (SlitBoxVertex n)) (hf : f ∈ (slitBoxGraph n).edgeSet) :
    ∃ a b, f = s(a,b) ∧ (slitBoxGraph n).Adj a b := by
  obtain ⟨ab, hab⟩ := Sym2.mk_surjective f
  have hab' : f = s(ab.1, ab.2) := by
    change f = Function.uncurry Sym2.mk ab
    exact hab.symm
  refine ⟨ab.1, ab.2, hab', ?_⟩
  apply (slitBoxGraph n).mem_edgeSet.mp
  rw [← hab']
  exact hf

private theorem incidentBond_face_memberships_iff
    (F : Finset LatticeVertex) (v : LatticeVertex) (b : LatticeBond)
    (hinc : v = b.source ∨ v = b.target)
    (hstar :
      ((v ∈ F) ↔ ((v.1 - 1, v.2) ∈ F)) ∧
      ((v ∈ F) ↔ ((v.1, v.2 - 1) ∈ F)) ∧
      (((v.1 - 1, v.2) ∈ F) ↔ ((v.1 - 1, v.2 - 1) ∈ F)) ∧
      (((v.1, v.2 - 1) ∈ F) ↔ ((v.1 - 1, v.2 - 1) ∈ F))) :
    ((b.faceBase true ∈ F) ↔ v ∈ F) ∧
      ((b.faceBase false ∈ F) ↔ v ∈ F) := by
  rcases incidentBond_eq_one_of_four v b hinc with hr | hu | hl | hd
  · subst b
    simp only [LatticeBond.faceBase]
    exact ⟨by simp, hstar.2.1.symm⟩
  · subst b
    simp only [LatticeBond.faceBase]
    exact ⟨by simp, hstar.1.symm⟩
  · subst b
    simp only [LatticeBond.faceBase]
    exact ⟨hstar.1.symm, hstar.2.2.1.symm.trans hstar.1.symm⟩
  · subst b
    simp only [LatticeBond.faceBase]
    exact ⟨hstar.2.1.symm, hstar.2.2.2.symm.trans hstar.2.1.symm⟩

/-- At a vertex with no incident cell-boundary edge, an actual slit edge is
incident-revealed exactly when the northeast cell base belongs to `F`. -/
theorem slitBoxCellIncidentEdges_iff_vertex_mem
    (n : ℕ) (F : Finset LatticeVertex) (v : SlitBoxVertex n)
    (hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v.val w)
    (e : (slitBoxGraph n).edgeSet) (hincident : v ∈ e.val) :
    e ∈ slitBoxCellIncidentEdges n F ↔ v.val ∈ F := by
  classical
  obtain ⟨a, b, hab, hadj⟩ := slitEdge_endpoint_data n e.val e.property
  have hvab : v = a ∨ v = b := by
    rw [hab] at hincident
    exact (Sym2.mem_iff').mp hincident
  have hsq : squareLattice.Adj a.val b.val := (slitBoxGraph_adj_iff n a b).mp hadj |>.1
  obtain ⟨bond, hbonds⟩ := LatticeBond.exists_of_adj hsq
  have heqMap : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val =
      s(a.val, b.val) := by
    rw [hab]
    simp
  have hbondSym : bond.toSym2 =
      Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val :=
    hbonds.trans heqMap.symm
  have hbondIncident : v.val = bond.source ∨ v.val = bond.target := by
    have hmem : v.val ∈ bond.toSym2 := by
      rw [hbondSym, heqMap]
      exact (Sym2.mem_iff').2 (hvab.elim (fun h => Or.inl (congrArg Subtype.val h))
        (fun h => Or.inr (congrArg Subtype.val h)))
    rw [LatticeBond.toSym2] at hmem
    exact (Sym2.mem_iff').mp hmem
  have hstar := latticeCellBoundaryGraph_isolated_vertex_four_cells_agree F v.val hNo
  have hface := incidentBond_face_memberships_iff F v.val bond hbondIncident hstar
  constructor
  · intro he
    obtain ⟨other, hbond, hfaceMem⟩ := (mem_slitBoxCellIncidentEdges n F e).mp he
    have hsame : other = bond := LatticeBond.toSym2_injective (hbond.trans hbondSym.symm)
    subst other
    rcases hfaceMem with ht | hf
    · exact hface.1.mp ht
    · exact hface.2.mp hf
  · intro hv
    apply (mem_slitBoxCellIncidentEdges n F e).mpr
    refine ⟨bond, hbondSym, ?_⟩
    exact Or.inl (hface.1.mpr hv)

/-- At a vertex satisfying the no-boundary-edge premise, all incident slit
edges have the same reveal status. -/
theorem slitBoxCellIncidentEdges_all_or_none_at_vertex
    (n : ℕ) (F : Finset LatticeVertex) (v : SlitBoxVertex n)
    (hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v.val w)
    (e f : (slitBoxGraph n).edgeSet)
    (he : v ∈ e.val) (hf : v ∈ f.val) :
    (e ∈ slitBoxCellIncidentEdges n F) ↔ (f ∈ slitBoxCellIncidentEdges n F) := by
  rw [slitBoxCellIncidentEdges_iff_vertex_mem n F v hNo e he,
    slitBoxCellIncidentEdges_iff_vertex_mem n F v hNo f hf]

/-- For the actual filling of a candidate polygon, every slit edge incident to
a box vertex off the candidate cycle has the same reveal status. -/
theorem slitBoxCellIncidentEdges_all_or_none_at_candidate_off_support
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hv : v.val ∉ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support)
    (e f : (slitBoxGraph n).edgeSet)
    (he : v ∈ e.val) (hf : v ∈ f.val) :
    (e ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)) ↔
    (f ∈ slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)) := by
  let c := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let F := (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ
  have hc : c.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  have hboundary : latticeCellBoundaryGraph F = c.toSubgraph.spanningCoe := by
    simpa [F, c, slitBoxFirstHitCandidatePolygon,
      slitBoxFirstHitCandidateCycle] using
        latticeCellBoundaryGraph_interiorCellBases_eq_cycle hc δ
  have hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v.val w := by
    intro w hadj
    have hEdge : s(v.val,w) ∈ (latticeCellBoundaryGraph F).edgeSet :=
      (latticeCellBoundaryGraph F).mem_edgeSet.mpr hadj
    rw [hboundary] at hEdge
    have hwalkEdge : s(v.val,w) ∈ c.edges := by
      have hiff : s(v.val,w) ∈ (c.toSubgraph.spanningCoe).edgeSet ↔
          s(v.val,w) ∈ c.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hEdge
    exact hv (c.fst_mem_support_of_mem_edges hwalkEdge)
  exact slitBoxCellIncidentEdges_all_or_none_at_vertex n F v hNo e f he hf

end PottsContinuity.FKC.FiniteFK
