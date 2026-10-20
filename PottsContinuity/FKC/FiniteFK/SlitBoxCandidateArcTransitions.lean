-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateArcTransitions.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateArcNeighbors
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open SimpleGraph

/-- A genuine crossing edge of an actual first-hit candidate cycle is the last
edge of its retained path: the first endpoint is the hit, and the other is the
penultimate path vertex. -/
theorem slitBoxFirstHitCandidateCycle_crossing_edge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u)
    {a b : SlitBoxVertex n}
    (ha : a ∈ slitBoxWiredArc n) (hb : b ∉ slitBoxWiredArc n)
    (he : s(a.val, b.val) ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges) :
    a = p.val.1 ∧
      b.val = (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate := by
  classical
  let w : (slitBoxGraph n).Walk u p.val.1 := p.val.2
  have hsq : squareLattice.Adj a.val b.val := by
    apply squareLattice.mem_edgeSet.mp
    exact (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges_subset_edgeSet he
  have hbCoords : ¬ (b.val.1 = 0 ∧ 0 ≤ b.val.2 ∧ b.val.2 ≤ (n : ℤ)) := by
    intro h
    exact hb ((mem_slitBoxWiredArc_iff n b).mpr h)
  have hnot : ¬ ((a.val.1 = 0 ∧ 0 ≤ a.val.2 ∧ a.val.2 ≤ (n : ℤ)) ∧
      (b.val.1 = 0 ∧ 0 ≤ b.val.2 ∧ b.val.2 ≤ (n : ℤ))) := by
    intro h
    exact hbCoords h.2
  have hadj : (slitBoxGraph n).Adj a b :=
    (slitBoxGraph_adj_iff n a b).2 ⟨hsq, hnot⟩
  let e : (slitBoxGraph n).edgeSet := ⟨s(a, b), (slitBoxGraph n).mem_edgeSet.mpr hadj⟩
  have he' : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges := by
    simpa [e] using he
  have hpEdge : e.val ∈ w.edges := by
    exact (slitBoxFirstHitCandidateCycle_slitEdge_mem_iff n hn u huY huX p e).mp he'
  have haSupport : a ∈ finiteSimplePathSupport p.val := by
    change a ∈ w.support
    exact w.fst_mem_support_of_mem_edges hpEdge
  have hfirst := p.property.2 a haSupport ha
  have haEq : a = p.val.1 := hfirst
  have hbPen : b.val = w.penultimate := by
    have hed : s(p.val.1, b) ∈ w.edges := by
      have hed' : s(a, b) ∈ w.edges := by simpa [w, e] using hpEdge
      simpa [haEq] using hed'
    have hpen := p.val.2.property.eq_penultimate_of_mem_edges hed
    exact congrArg Subtype.val hpen
  exact ⟨haEq, hbPen⟩

/-- A crossing edge in the union of the two actual candidate cycles is supplied
by one of those candidates, with that candidate's genuine first-hit endpoint. -/
theorem slitBoxFirstHitCandidateCycle_union_crossing_edge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p q : SlitBoxFirstHitBaseCandidates n u)
    {a b : SlitBoxVertex n}
    (ha : a ∈ slitBoxWiredArc n) (hb : b ∉ slitBoxWiredArc n)
    (he : s(a.val, b.val) ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges ∨
      s(a.val, b.val) ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges) :
    (a = p.val.1 ∧ b.val = (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate) ∨
    (a = q.val.1 ∧ b.val = (q.val.2 : (slitBoxGraph n).Walk u q.val.1).penultimate) := by
  rcases he with hp | hq
  · exact Or.inl (slitBoxFirstHitCandidateCycle_crossing_edge
      n hn u huY huX p ha hb hp)
  · exact Or.inr (slitBoxFirstHitCandidateCycle_crossing_edge
      n hn u huY huX q ha hb hq)

/-- Every actual union crossing bond is one of the two actual terminal bonds
of the retained first-hit paths. The finite set deliberately keeps both ports
when the hit vertices coincide. -/
theorem slitBoxFirstHitCandidateCycle_union_crossing_edge_mem_two_ports
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p q : SlitBoxFirstHitBaseCandidates n u)
    {a b : SlitBoxVertex n}
    (ha : a ∈ slitBoxWiredArc n) (hb : b ∉ slitBoxWiredArc n)
    (he : s(a.val, b.val) ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges ∨
      s(a.val, b.val) ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges) :
    s(a.val, b.val) ∈ ({s(p.val.1.val,
        (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate.val),
      s(q.val.1.val,
        (q.val.2 : (slitBoxGraph n).Walk u q.val.1).penultimate.val)} :
        Finset (Sym2 LatticeVertex)) := by
  rcases slitBoxFirstHitCandidateCycle_union_crossing_edge
      n hn u huY huX p q ha hb he with hp | hq
  · have hstart : a.val = p.val.1.val := congrArg Subtype.val hp.1
    rw [hstart, hp.2]
    simp
  · have hstart : a.val = q.val.1.val := congrArg Subtype.val hq.1
    rw [hstart, hq.2]
    simp

/-- The set of the two genuine candidate ports has at most two bonds, even
when coincident hit vertices make the candidate bonds coincide. -/
theorem slitBoxFirstHitCandidateCycle_two_port_bonds_card_le_two
    (n : ℕ) (u : SlitBoxVertex n)
    (p q : SlitBoxFirstHitBaseCandidates n u) :
    ({s(p.val.1.val,
        (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate.val),
      s(q.val.1.val,
        (q.val.2 : (slitBoxGraph n).Walk u q.val.1).penultimate.val)} :
        Finset (Sym2 LatticeVertex)).card ≤ 2 := Finset.card_le_two

end PottsContinuity.FKC.FiniteFK
