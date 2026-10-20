-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateIntersectionRightBoundary.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateRightStrip
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryCriterion
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

def intersectionRightBoundaryBaseHom (n : ℕ)
    (A : Configuration (slitBoxGraph n)) [Fintype (slitBoxGraph n).edgeSet
    ] (hA : A = Finset.univ) :
    slitBoxGraph n →g openGraph (slitBoxGraph n) A where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply (openGraph_adj (slitBoxGraph n) A x y).2
    change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
    rw [hA]
    refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
    exact Finset.mem_univ _

/-- The true intersection of two candidate interiors has every canonical
right return bond on its actual lattice-cell boundary. -/
theorem slitBoxFirstHitCandidateIntersection_right_boundary
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (j : ℤ) (hlo : -(n + 1 : ℤ) ≤ j) (hhi : j ≤ (n : ℤ)) :
    let Pp := slitBoxFirstHitCandidatePolygon n hn u huY huX p
    let Pq := slitBoxFirstHitCandidatePolygon n hn u huY huX q
    let F := Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ
    Medial.LatticeBond.mk ((n + 1 : ℤ), j) .vertical ∈ latticeCellBoundaryBonds F := by
  classical
  let Pp := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let Pq := slitBoxFirstHitCandidatePolygon n hn u huY huX q
  let F := Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ
  let e : Medial.LatticeBond := ⟨((n + 1 : ℤ), j), .vertical⟩
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := intersectionRightBoundaryBaseHom n A hA
  let t := p.val.1
  let r := slitBoxCanonicalReturnWalk n u huY huX t p.property.1
  let preWalk : squareLattice.Walk u.val t.val :=
    (((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A))
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX p = preWalk.append r := by
    rfl
  have hr := slitBoxCanonicalReturnWalk_right_edge_mem n u huY huX t p.property.1 j hlo hhi
  have hmemList : s(((n + 1 : ℤ), j), ((n + 1 : ℤ), j + 1)) ∈
      preWalk.edges ++ r.edges := List.mem_append.mpr (Or.inr hr)
  have heEdge : e.toSym2 ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges := by
    rw [hcycle, SimpleGraph.Walk.edges_append]
    simpa [e, Medial.LatticeBond.toSym2, Medial.LatticeBond.source,
      Medial.LatticeBond.target] using hmemList
  have hcy := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  obtain ⟨i, hi⟩ := (latticePolygonOfCycle_edge_iff hcy e.toSym2).mp heEdge
  have hboundaryEq : e.toSym2 = s(Pp.vertex i, Pp.vertex (i + 1)) := by
    simpa [Pp, slitBoxFirstHitCandidatePolygon] using hi
  have hboundary : e = Pp.boundaryBond i := (Pp.eq_boundaryBond_iff i e).mpr hboundaryEq
  have hdiff := (Pp.cellCenters_differ_iff_boundaryBond δ e).2 ⟨i, hboundary⟩
  have hdiff' :
      (latticeCellCenter δ ((n + 1 : ℤ), j) ∈ Pp.domain δ) ≠
        (latticeCellCenter δ ((n : ℤ), j) ∈ Pp.domain δ) := by
    simpa [e, Medial.LatticeBond.faceBase] using hdiff
  have hleftP : latticeCellCenter δ ((n : ℤ), j) ∈ Pp.domain δ :=
    slitBoxFirstHitCandidate_right_strip_inside n hn u huY huX δ p j hlo hhi
  have hleftQ : latticeCellCenter δ ((n : ℤ), j) ∈ Pq.domain δ :=
    slitBoxFirstHitCandidate_right_strip_inside n hn u huY huX δ q j hlo hhi
  have hrightP : latticeCellCenter δ ((n + 1 : ℤ), j) ∉ Pp.domain δ := by
    intro hr
    exact hdiff' (propext (iff_of_true hr hleftP))
  have hleftMemQ : ((n : ℤ), j) ∈ Pp.interiorCellBases δ ∩ Pq.interiorCellBases δ := by
    rw [Finset.mem_inter, Pp.mem_interiorCellBases_iff, Pq.mem_interiorCellBases_iff]
    exact ⟨hleftP, hleftQ⟩
  have hrightNotF : ((n + 1 : ℤ), j) ∉ F := by
    intro h
    have hP : ((n + 1 : ℤ), j) ∈ Pp.interiorCellBases δ := (Finset.mem_inter.mp h).1
    have hdom := Pp.mem_interiorCellBases_iff δ ((n + 1 : ℤ), j) |>.mp hP
    exact hrightP hdom
  have hleftInF : ((n : ℤ), j) ∈ F := by
    exact hleftMemQ
  have hfaceDiff :
      ((e.faceBase true) ∈ F) ≠ ((e.faceBase false) ∈ F) := by
    have htrue : e.faceBase true ∉ F := by
      simpa [e, Medial.LatticeBond.faceBase] using hrightNotF
    have hfalse : e.faceBase false ∈ F := by
      simpa [e, Medial.LatticeBond.faceBase] using hleftInF
    intro heq
    exact htrue (heq ▸ hfalse)
  exact (mem_latticeCellBoundaryBonds F e).mpr hfaceDiff

/-- The same literal right return bonds are edges of the graph built from the
actual intersection boundary. -/
theorem slitBoxFirstHitCandidateIntersection_right_boundaryGraph_adj
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (j : ℤ) (hlo : -(n + 1 : ℤ) ≤ j) (hhi : j ≤ (n : ℤ)) :
    let F :=
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
        (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
    (latticeCellBoundaryGraph F).Adj ((n + 1 : ℤ), j) ((n + 1 : ℤ), j + 1) := by
  classical
  let F :=
    (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
      (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ
  let e : Medial.LatticeBond := ⟨((n + 1 : ℤ), j), .vertical⟩
  have hbond := slitBoxFirstHitCandidateIntersection_right_boundary
    n hn u huY huX δ p q j hlo hhi
  have hmem : e ∈ latticeCellBoundaryBonds F := by
    simpa [e, F] using hbond
  rw [latticeCellBoundaryGraph_adj_iff]
  refine ⟨e.adjacent, e, ?_, ?_⟩
  · simp [e, Medial.LatticeBond.toSym2, Medial.LatticeBond.source,
      Medial.LatticeBond.target]
  · exact (mem_latticeCellBoundaryBonds F e).mp hmem

end PottsContinuity.FKC.FiniteFK
