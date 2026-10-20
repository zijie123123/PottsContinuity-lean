-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateFillingInjective.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import PottsContinuity.FKC.Domains.LatticePolygonCellFillingBoundary
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.FiniteFK.SimplePathEdgeSetUniqueness
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial PottsContinuity.FKC.LatticePolygon

theorem slitBoxFirstHitCandidateInteriorCells_injective
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) :
    Function.Injective (slitBoxFirstHitCandidateInteriorCells n hn u huY huX δ) := by
  classical
  let : Fintype (SlitBoxVertex n) := Fintype.ofFinite _
  let : DecidableEq (SlitBoxVertex n) := Classical.decEq _
  let : DecidableRel (slitBoxGraph n).Adj := Classical.decRel _
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  intro p q hfill
  let cP := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cQ := slitBoxFirstHitCandidateCycle n hn u huY huX q
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let Q := slitBoxFirstHitCandidatePolygon n hn u huY huX q
  have hcP : cP.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  have hcQ : cQ.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX q
  have hboundary (e : LatticeBond) :
      (∃ i : ZMod ((cP.length - 3) + 3), e = P.boundaryBond i) ↔
        (∃ j : ZMod ((cQ.length - 3) + 3), e = Q.boundaryBond j) := by
    exact boundaryBondSet_eq_of_interiorCellBases_eq P Q δ hfill e
  have hcycleEdges : ∀ e : Sym2 LatticeVertex,
      e ∈ cP.edges ↔ e ∈ cQ.edges := by
    intro e
    change e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges ↔
      e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges
    rw [latticePolygonOfCycle_edge_iff hcP, latticePolygonOfCycle_edge_iff hcQ]
    constructor
    · rintro ⟨i, hi⟩
      have hPmem : ∃ k : ZMod ((cP.length - 3) + 3),
          P.boundaryBond i = P.boundaryBond k := ⟨i, rfl⟩
      obtain ⟨j, hPQ⟩ := (hboundary (P.boundaryBond i)).mp hPmem
      have hsym := congrArg LatticeBond.toSym2 hPQ
      refine ⟨j, ?_⟩
      calc
        e = s(P.vertex i, P.vertex (i + 1)) := hi
        _ = (P.boundaryBond i).toSym2 := (P.boundaryBond_toSym2 i).symm
        _ = (Q.boundaryBond j).toSym2 := hsym
        _ = s(Q.vertex j, Q.vertex (j + 1)) := Q.boundaryBond_toSym2 j
    · rintro ⟨j, hj⟩
      have hQmem : ∃ k : ZMod ((cQ.length - 3) + 3),
          Q.boundaryBond j = Q.boundaryBond k := ⟨j, rfl⟩
      obtain ⟨i, hQP⟩ := (hboundary (Q.boundaryBond j)).symm.mp hQmem
      have hsym := congrArg LatticeBond.toSym2 hQP
      refine ⟨i, ?_⟩
      calc
        e = s(Q.vertex j, Q.vertex (j + 1)) := hj
        _ = (Q.boundaryBond j).toSym2 := (Q.boundaryBond_toSym2 j).symm
        _ = (P.boundaryBond i).toSym2 := hsym
        _ = s(P.vertex i, P.vertex (i + 1)) := P.boundaryBond_toSym2 i
  have hbaseEdges : ∀ e : Sym2 (SlitBoxVertex n),
      e ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges ↔
        e ∈ (q.val.2 : (slitBoxGraph n).Walk u q.val.1).edges := by
    intro e
    by_cases he : e ∈ (slitBoxGraph n).edgeSet
    · let eb : (slitBoxGraph n).edgeSet := ⟨e, he⟩
      have hPedge := slitBoxFirstHitCandidateCycle_slitEdge_mem_iff
        n hn u huY huX p eb
      have hQedge := slitBoxFirstHitCandidateCycle_slitEdge_mem_iff
        n hn u huY huX q eb
      have hPedge' : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e ∈
          cP.edges ↔ e ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges := by
        simpa [cP, eb] using hPedge
      have hQedge' : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e ∈
          cQ.edges ↔ e ∈ (q.val.2 : (slitBoxGraph n).Walk u q.val.1).edges := by
        simpa [cQ, eb] using hQedge
      exact hPedge'.symm.trans ((hcycleEdges _).trans hQedge')
    · constructor
      · intro heP
        exact (he (SimpleGraph.Walk.edges_subset_edgeSet _ heP)).elim
      · intro heQ
        exact (he (SimpleGraph.Walk.edges_subset_edgeSet _ heQ)).elim
  have hpaths := simplePath_support_eq_of_edgeMembership_eq
    (p.val.2 : (slitBoxGraph n).Walk u p.val.1)
    (q.val.2 : (slitBoxGraph n).Walk u q.val.1)
    p.val.2.property q.val.2.property hbaseEdges
  have hbase : p.val = q.val :=
    (finiteSimplePathSupport_injective (G := slitBoxGraph n) u) hpaths.1
  exact Subtype.ext hbase

end PottsContinuity.FKC.FiniteFK
