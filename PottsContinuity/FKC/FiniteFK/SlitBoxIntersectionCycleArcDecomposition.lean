-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxIntersectionCycleArcDecomposition.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxIntersectionCycleInsidePath
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateArcTransitions
public import PottsContinuity.FKC.Medial.SimplePathTwoEdgeCut
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Split the actual inside complementary path of an intersection-boundary
cycle at its first hit of the wired arc. The tail stays on the wired arc, and
both pieces remain actual subpaths of the same boundary cycle. -/
theorem slitBoxFirstHitIntersectionCycle_inside_path_arc_decomposition
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex} (c : squareLattice.Walk z z) (hc : c.IsCycle)
    (hcommon : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges)
    (hboundary : ∀ e ∈ c.edges,
      e ∈ (latticeCellBoundaryGraph
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) :
    let A : Set LatticeVertex := {x | x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ n}
    let F : Finset (Sym2 LatticeVertex) :=
      {s(p.val.1.val, (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate.val),
       s(q.val.1.val, (q.val.2 : (slitBoxGraph n).Walk u q.val.1).penultimate.val)}
    ∃ s : squareLattice.Walk u.val (slitBoxTopArcVertex n).val,
      s.IsPath ∧
      (∀ x ∈ s.support, x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) ∧
      (∀ a b, s(a,b) ∈ s.edges →
        ((a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) → s(a,b) ∈ F) ∧
      (∃ b : LatticeVertex, b ∈ A ∧
        ∃ prePath : squareLattice.Walk u.val b,
        ∃ arcTail : squareLattice.Walk b (slitBoxTopArcVertex n).val,
          prePath.IsPath ∧ arcTail.IsPath ∧ prePath.append arcTail = s ∧
          (∀ x ∈ prePath.support, x ∈ A → x = b) ∧
          (∀ x ∈ arcTail.support, x ∈ A) ∧
          (∀ x ∈ prePath.support,
            x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) ∧
          (∀ x ∈ arcTail.support,
            x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) ∧
          (∀ e, e ∈ prePath.edges → e ∈ s.edges) ∧
          (∀ e, e ∈ arcTail.edges → e ∈ s.edges) ∧
          (∀ e, e ∈ prePath.edges → e ∈ c.edges) ∧
          (∀ e, e ∈ arcTail.edges → e ∈ c.edges)) ∧
      List.Disjoint
        (slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges s.edges ∧
      ((slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).append s).IsCycle ∧
      (∀ e, e ∈ c.edges → e ∈
        (slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges ∨
        e ∈ s.edges) ∧
      (∀ e, e ∈
        (slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges → e ∈ c.edges) ∧
      (∀ e, e ∈ s.edges → e ∈ c.edges) ∧
      (∀ e, e ∈
        (slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges ∨
        e ∈ s.edges → e ∈ c.edges) ∧
      (∀ e ∈ c.edges,
        e ∈ (latticeCellBoundaryGraph
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
            (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) := by
  classical
  dsimp
  let A : Set LatticeVertex := {x | x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ n}
  let F : Finset (Sym2 LatticeVertex) :=
    {s(p.val.1.val, (p.val.2 : (slitBoxGraph n).Walk u p.val.1).penultimate.val),
     s(q.val.1.val, (q.val.2 : (slitBoxGraph n).Walk u q.val.1).penultimate.val)}
  obtain ⟨s, hsPath, hsBox, hdisj, hcover, hback, hsCycle, hRinC, hboundary'⟩ :=
    slitBoxFirstHitIntersectionCycle_has_inside_complementary_path
      n hn u huY huX δ p q c hc hcommon hboundary
  have huNotA : u.val ∉ A := by
    intro hu
    have hy : 0 ≤ u.val.2 := hu.2.1
    rw [huY] at hy
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    omega
  have htopA : (slitBoxTopArcVertex n).val ∈ A := by
    simp [A, slitBoxTopArcVertex]
  have hFcard : F.card ≤ 2 := by
    simpa [F] using slitBoxFirstHitCandidateCycle_two_port_bonds_card_le_two n u p q
  have hcut : ∀ a b, s(a,b) ∈ s.edges →
      ((a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) → s(a,b) ∈ F := by
    intro a b he hcross
    have haSupport : a ∈ s.support := s.fst_mem_support_of_mem_edges he
    have hbSupport : b ∈ s.support := s.snd_mem_support_of_mem_edges he
    have haBox := hsBox a haSupport
    have hbBox := hsBox b hbSupport
    let va : SlitBoxVertex n := ⟨a, haBox⟩
    let vb : SlitBoxVertex n := ⟨b, hbBox⟩
    have heC : s(a,b) ∈ c.edges := hback (s(a,b)) (Or.inr he)
    have hcycleEdges := slitBoxFirstHitCandidateIntersection_cycle_edges_subset_union
      n hn u huY huX δ p q c hc hboundary (s(a,b)) heC
    have hports : s(a,b) ∈ F := by
      rcases hcycleEdges with hP | hQ
      · rcases hcross with hAB | hBA
        · have hArc : va ∈ slitBoxWiredArc n :=
            (mem_slitBoxWiredArc_iff n va).2 (by simpa [A, va] using hAB.1)
          have hOutside : vb ∉ slitBoxWiredArc n := by
            intro hmem
            exact hAB.2 (by simpa [A, vb] using (mem_slitBoxWiredArc_iff n vb).1 hmem)
          have hEdge : s(va.val, vb.val) ∈
              (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges := by
            simpa [va, vb] using hP
          have hmem := slitBoxFirstHitCandidateCycle_union_crossing_edge_mem_two_ports
            n hn u huY huX p q hArc hOutside (Or.inl hEdge)
          simpa [F, va, vb] using hmem
        · have hArc : vb ∈ slitBoxWiredArc n :=
            (mem_slitBoxWiredArc_iff n vb).2 (by simpa [A, vb] using hBA.2)
          have hOutside : va ∉ slitBoxWiredArc n := by
            intro hmem
            exact hBA.1 (by simpa [A, va] using (mem_slitBoxWiredArc_iff n va).1 hmem)
          have hEdge : s(vb.val, va.val) ∈
              (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges := by
            have hswap : s(b,a) = s(a,b) := Sym2.eq_swap ..
            simpa [va, vb, hswap] using hP
          have hmem := slitBoxFirstHitCandidateCycle_union_crossing_edge_mem_two_ports
            n hn u huY huX p q hArc hOutside (Or.inl hEdge)
          have hswap : s(b,a) = s(a,b) := Sym2.eq_swap ..
          simpa [F, va, vb, hswap] using hmem
      · rcases hcross with hAB | hBA
        · have hArc : va ∈ slitBoxWiredArc n :=
            (mem_slitBoxWiredArc_iff n va).2 (by simpa [A, va] using hAB.1)
          have hOutside : vb ∉ slitBoxWiredArc n := by
            intro hmem
            exact hAB.2 (by simpa [A, vb] using (mem_slitBoxWiredArc_iff n vb).1 hmem)
          have hEdge : s(va.val, vb.val) ∈
              (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges := by
            simpa [va, vb] using hQ
          have hmem := slitBoxFirstHitCandidateCycle_union_crossing_edge_mem_two_ports
            n hn u huY huX p q hArc hOutside (Or.inr hEdge)
          simpa [F, va, vb] using hmem
        · have hArc : vb ∈ slitBoxWiredArc n :=
            (mem_slitBoxWiredArc_iff n vb).2 (by simpa [A, vb] using hBA.2)
          have hOutside : va ∉ slitBoxWiredArc n := by
            intro hmem
            exact hBA.1 (by simpa [A, va] using (mem_slitBoxWiredArc_iff n va).1 hmem)
          have hEdge : s(vb.val, va.val) ∈
              (slitBoxFirstHitCandidateCycle n hn u huY huX q).edges := by
            have hswap : s(b,a) = s(a,b) := Sym2.eq_swap ..
            simpa [va, vb, hswap] using hQ
          have hmem := slitBoxFirstHitCandidateCycle_union_crossing_edge_mem_two_ports
            n hn u huY huX p q hArc hOutside (Or.inr hEdge)
          have hswap : s(b,a) = s(a,b) := Sym2.eq_swap ..
          simpa [F, va, vb, hswap] using hmem
    exact hports
  obtain ⟨b, hb, prePath, arcTail, hpPath, htPath, hsplit, hfirst, htailA,
      hpEdges, htEdges⟩ :=
    PottsContinuity.FKC.Medial.walk_exists_first_hit_decomposition_of_two_edge_cut
      F hFcard s hcut huNotA htopA hsPath
  have hprePathBox : ∀ x ∈ prePath.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    intro x hx
    have hxS : x ∈ s.support := by
      have hsupp := SimpleGraph.Walk.support_subset_support_append_left prePath arcTail
      rw [hsplit] at hsupp
      exact hsupp hx
    exact hsBox x hxS
  have htailBox : ∀ x ∈ arcTail.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    intro x hx
    have hxS : x ∈ s.support := by
      have hsupp := SimpleGraph.Walk.support_subset_support_append_right prePath arcTail
      rw [hsplit] at hsupp
      exact hsupp hx
    exact hsBox x hxS
  have hpInC : ∀ e, e ∈ prePath.edges → e ∈ c.edges := by
    intro e he
    exact hback e (Or.inr (hpEdges e he))
  have htInC : ∀ e, e ∈ arcTail.edges → e ∈ c.edges := by
    intro e he
    exact hback e (Or.inr (htEdges e he))
  have hsInC : ∀ e, e ∈ s.edges → e ∈ c.edges := by
    intro e he
    exact hback e (Or.inr he)
  refine ⟨s, hsPath, hsBox, hcut, ?_, hdisj, hsCycle, hcover, hRinC,
    hsInC, hback, hboundary'⟩
  exact ⟨b, hb, prePath, arcTail, hpPath, htPath, hsplit, hfirst, htailA,
    hprePathBox, htailBox, hpEdges, htEdges, hpInC, htInC⟩

end PottsContinuity.FKC.FiniteFK
