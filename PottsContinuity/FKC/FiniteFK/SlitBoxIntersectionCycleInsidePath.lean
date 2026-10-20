-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxIntersectionCycleInsidePath.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxIntersectionCycleCommonReturn
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateExteriorSupport
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionCycleUnion
public import PottsContinuity.FKC.Medial.CycleComplementaryPathInside
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The common exterior return and its complementary arc in a genuine
intersection-boundary cycle split that cycle exactly. The complementary arc
stays in the literal slit box, and the boundary-edge witness remains explicit
for later edge-state tracing. -/
theorem slitBoxFirstHitIntersectionCycle_has_inside_complementary_path
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex} (c : squareLattice.Walk z z) (hc : c.IsCycle)
    (hcommon : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges)
    (hboundary : ∀ e ∈ c.edges,
      e ∈ (latticeCellBoundaryGraph
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) :
    let R := slitBoxCanonicalReturnWalk n u huY huX
      (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)
    ∃ s : squareLattice.Walk u.val (slitBoxTopArcVertex n).val,
      s.IsPath ∧
      (∀ x ∈ s.support,
        x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) ∧
      List.Disjoint R.edges s.edges ∧
      (∀ e, e ∈ c.edges → e ∈ R.edges ∨ e ∈ s.edges) ∧
      (∀ e, e ∈ R.edges ∨ e ∈ s.edges → e ∈ c.edges) ∧
      (R.append s).IsCycle ∧
      (∀ e ∈ R.edges, e ∈ c.edges) ∧
      (∀ e ∈ c.edges,
        e ∈ (latticeCellBoundaryGraph
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
            (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) := by
  classical
  dsimp
  let R := slitBoxCanonicalReturnWalk n u huY huX
    (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  have hcommonReturn := slitBoxFirstHitIntersectionCycle_contains_canonical_top_return
    n hn u huY huX δ p q c hc hcommon hboundary
  have hRpath : R.IsPath := by
    simpa [R] using slitBoxCanonicalTopReturnWalk_isPath n hn u huY huX
  have hRinC : ∀ e ∈ R.edges, e ∈ c.edges := by
    simpa [R] using hcommonReturn.2.2
  have hcycleEdges := slitBoxFirstHitCandidateIntersection_cycle_edges_subset_union
    n hn u huY huX δ p q c hc hboundary
  have houtside : ∀ x, x ∈ c.support →
      x ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) → x ∈ R.support := by
    intro x hx hxOut
    obtain ⟨e, he, hxe⟩ :=
      (c.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
    rcases Sym2.mk_surjective e with ⟨⟨a, b⟩, rfl⟩
    have hendpoint : x = a ∨ x = b := by simpa using hxe
    have hside := hcycleEdges (s(a,b)) he
    rcases hside with hP | hQ
    · have hxP : x ∈ cp.support := by
        rcases hendpoint with rfl | rfl
        · exact cp.fst_mem_support_of_mem_edges hP
        · exact cp.snd_mem_support_of_mem_edges hP
      have hxTop := slitBoxFirstHitCandidateCycle_outside_support_subset_top
        n hn u huY huX p (by simpa [cp] using hxP) hxOut
      simpa [R] using hxTop
    · have hxQ : x ∈ cq.support := by
        rcases hendpoint with rfl | rfl
        · exact cq.fst_mem_support_of_mem_edges hQ
        · exact cq.snd_mem_support_of_mem_edges hQ
      have hxTop := slitBoxFirstHitCandidateCycle_outside_support_subset_top
        n hn u huY huX q (by simpa [cq] using hxQ) hxOut
      simpa [R] using hxTop
  have htopBox : (slitBoxTopArcVertex n).val ∈
      latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    rw [mem_latticeRectangle]
    simp only [slitBoxTopArcVertex]
    push_cast
    constructor <;> constructor <;> omega
  have huBox : u.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) :=
    u.property
  have hneq : (slitBoxTopArcVertex n).val ≠ u.val := by
    intro heq
    have hy := congrArg Prod.snd heq
    simp only [slitBoxTopArcVertex] at hy
    omega
  obtain ⟨s, hsPath, hsBox, hdisj, hcover, hback, hsCycle⟩ :=
    PottsContinuity.FKC.Medial.exists_complementary_path_support_subset
      hneq c hc R hRpath hRinC
      (latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) htopBox huBox houtside
  exact ⟨s, hsPath, hsBox, hdisj, hcover, hback, hsCycle, hRinC, hboundary⟩

end PottsContinuity.FKC.FiniteFK
