-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxIntersectionCycleCandidate.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxIntersectionCycleArcDecomposition
public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitCandidateLift
public import PottsContinuity.FKC.FiniteFK.SlitBoxArcPathUniqueness
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnArcSplit
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Reconstruct an actual first-hit candidate whose canonical cycle has exactly
the same edges as the given intersection cycle. -/
theorem slitBoxFirstHitIntersectionCycle_actual_candidate_reconstruction
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex} (c : squareLattice.Walk z z) (hc : c.IsCycle)
    (hcommon : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges)
    (hboundary : ∀ e ∈ c.edges,
      e ∈ (latticeCellBoundaryGraph
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) :
    ∃ r : SlitBoxFirstHitBaseCandidates n u,
      ∀ e, e ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX r).edges ↔ e ∈ c.edges := by
  classical
  obtain ⟨s, hsPath, hsBox, hcut,
      ⟨b, hb, prePath, arcTail, hprePath, htailPath, hsplit, hfirst, htailA,
        hpreBox, htailBox, hpreToS, htailToS, hpreToC, htailToC⟩,
      hdisj, hsCycle, hcover, hRtoC, hsToC, hback, hboundary'⟩ :=
    slitBoxFirstHitIntersectionCycle_inside_path_arc_decomposition
      n hn u huY huX δ p q c hc hcommon hboundary
  have hbBox : b ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    exact hpreBox b prePath.end_mem_support
  let t : SlitBoxVertex n := ⟨b, hbBox⟩
  have htArc : t ∈ slitBoxWiredArc n := by
    exact (mem_slitBoxWiredArc_iff n t).2 (by simpa [t] using hb)
  have hfirst' : ∀ x ∈ prePath.support,
      (x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ n) → x = t.val := by
    intro x hx hxA
    exact hfirst x hx hxA
  obtain ⟨r, hrt, hmap⟩ :=
    slitBoxFirstHitCandidate_of_bounded_first_hit_walk n u t htArc
      prePath hprePath hpreBox hfirst'
  have htailSupport : ∀ x ∈ arcTail.support,
      ∃ v : SlitBoxVertex n, v ∈ slitBoxWiredArc n ∧ v.val = x := by
    intro x hx
    have hxA := htailA x hx
    have hxBox := htailBox x hx
    let v : SlitBoxVertex n := ⟨x, hxBox⟩
    exact ⟨v, (mem_slitBoxWiredArc_iff n v).2 (by simpa [v] using hxA), rfl⟩
  have htR : r.val.1 ∈ slitBoxWiredArc n := by
    rw [hrt]
    exact htArc
  have hstart : r.val.1.val = b := by
    simpa [t] using congrArg (fun v : SlitBoxVertex n => v.val) hrt
  have htailCopy : arcTail.copy hstart.symm rfl =
      slitBoxArcVerticalWalk n r.val.1 htR := by
    have hcopyPath : (arcTail.copy hstart.symm rfl).IsPath := by
      simpa using htailPath
    have hcopySupport : ∀ x ∈ (arcTail.copy hstart.symm rfl).support,
        ∃ v : SlitBoxVertex n, v ∈ slitBoxWiredArc n ∧ v.val = x := by
      intro x hx
      have hx' : x ∈ arcTail.support := by simpa using hx
      exact htailSupport x hx'
    exact slitBoxWiredArc_simple_path_eq_literal n r.val.1 htR
      (arcTail.copy hstart.symm rfl) hcopyPath hcopySupport
  have hreturnEdges :
      (slitBoxCanonicalReturnWalk n u huY huX r.val.1 r.property.1).edges =
        arcTail.edges ++
          (slitBoxCanonicalReturnWalk n u huY huX
            (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges := by
    have hsplitR := slitBoxCanonicalReturnWalk_eq_arcVertical_append_topReturn
      n u huY huX r.val.1 htR
    calc
      _ = ((slitBoxArcVerticalWalk n r.val.1 htR).append
          (slitBoxCanonicalReturnWalk n u huY huX
            (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n))).edges :=
            congrArg SimpleGraph.Walk.edges hsplitR
      _ = arcTail.edges ++
          (slitBoxCanonicalReturnWalk n u huY huX
            (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges := by
            rw [SimpleGraph.Walk.edges_append, ← htailCopy]
            simp only [SimpleGraph.Walk.edges_copy]
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f : slitBoxGraph n →g openGraph (slitBoxGraph n) A := {
    toFun := id
    map_rel' := by
      intro x y hxy
      apply (openGraph_adj (slitBoxGraph n) A x y).2
      change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
      rw [hA]
      exact ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩,
        Finset.mem_univ _, rfl⟩ }
  let prefixWalk : squareLattice.Walk u.val r.val.1.val :=
    (((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A))
  have hprefixEdges : prefixWalk.edges = prePath.edges := by
    have hbase :
        ((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map
          (slitBoxUnderlyingToSquareHom n)).edges = prePath.edges := by
      have h := congrArg SimpleGraph.Walk.edges hmap
      have hcopy :
          (((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map
            (slitBoxUnderlyingToSquareHom n)).copy rfl
              (congrArg Subtype.val hrt)).edges =
            ((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map
              (slitBoxUnderlyingToSquareHom n)).edges :=
        SimpleGraph.Walk.edges_copy _ _ _
      exact hcopy.symm.trans h
    calc
      prefixWalk.edges =
          ((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map
            (slitBoxUnderlyingToSquareHom n)).edges := by
        dsimp [prefixWalk, f]
        rw [SimpleGraph.Walk.map_map]
        congr 1
      _ = prePath.edges := hbase
  let ret := slitBoxCanonicalReturnWalk n u huY huX r.val.1 r.property.1
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX r = prefixWalk.append ret := by
    dsimp [prefixWalk, ret, slitBoxFirstHitCandidateCycle, f]
    rfl
  have hsEdges : s.edges = prePath.edges ++ arcTail.edges := by
    simpa only [SimpleGraph.Walk.edges_append] using
      (congrArg SimpleGraph.Walk.edges hsplit).symm
  refine ⟨r, ?_⟩
  intro e
  rw [hcycle, SimpleGraph.Walk.edges_append, hprefixEdges, hreturnEdges]
  constructor
  · intro he
    rcases List.mem_append.mp he with hpre | htailOrR
    · exact hpreToC e hpre
    · rcases List.mem_append.mp htailOrR with htail | hR
      · exact htailToC e htail
      · exact hRtoC e hR
  · intro he
    rcases hcover e he with hR | hs
    · exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hR)))
    · rw [hsEdges] at hs
      rcases List.mem_append.mp hs with hpre | htail
      · exact List.mem_append.mpr (Or.inl hpre)
      · exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr (Or.inl htail)))

end PottsContinuity.FKC.FiniteFK

