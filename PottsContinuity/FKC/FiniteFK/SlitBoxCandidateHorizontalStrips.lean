-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateHorizontalStrips.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxFinitePolygonCandidates
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryCriterion
public import PottsContinuity.FKC.Domains.LatticePolygonVerticalBounds
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

def horizontalStripBaseHom (n : ℕ)
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

private theorem return_support_y_bounds (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxExteriorReturnWalkNat n a k ha hk).val.support) :
    -(n + 1 : ℤ) ≤ z.2 ∧ z.2 ≤ (n + 1 : ℤ) := by
  unfold slitBoxExteriorReturnWalkNat at hz
  dsimp only at hz
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz1 | hz
  · obtain ⟨_, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds 0 (k : ℤ)
      (n + 1 - k) (by simpa only [SimpleGraph.Walk.support_copy] using hz1)
    have hsum : (k : ℤ) + ((n + 1 - k : ℕ) : ℤ) = (n + 1 : ℤ) := by
      rw [Nat.cast_sub (by omega : k ≤ n + 1)]
      push_cast
      omega
    rw [hsum] at hhi
    constructor <;> omega
  · rcases hz with hz2 | hz
    · obtain ⟨hy, _, _⟩ := slitReturnHorizontalRightWalk_support_bounds 0
        (n + 1 : ℤ) (n + 1) (by simpa [SimpleGraph.Walk.support_copy] using hz2)
      rw [hy]
      constructor <;> omega
    · rcases hz with hz3 | hz
      · obtain ⟨_, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
          (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1)) (by
            simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz3)
        have hsum : -(n + 1 : ℤ) + ((2 * (n + 1) : ℕ) : ℤ) = (n + 1 : ℤ) := by
          push_cast
          omega
        rw [hsum] at hhi
        exact ⟨hlo, hhi⟩
      · rcases hz with hz4 | hz5
        · obtain ⟨hy, _, _⟩ := slitReturnHorizontalRightWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) (n + 1 - a) (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz4)
          rw [hy]
          constructor <;> omega
        · obtain ⟨_, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) 1 (by
              simpa [SimpleGraph.Walk.support_copy] using hz5)
          constructor <;> omega

private theorem candidate_vertex_y_bounds (n : ℕ) (hn : 1 ≤ n)
    (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (i : ZMod ((slitBoxFirstHitCandidateCycle n hn u huY huX p).length - 3 + 3)) :
    -(n + 1 : ℤ) ≤ ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).vertex i).2 ∧
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).vertex i).2 ≤ (n + 1 : ℤ) := by
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := horizontalStripBaseHom n A hA
  let pOpen : (openGraph (slitBoxGraph n) A).Walk u p.val.1 :=
    (p.val.2 : (slitBoxGraph n).Walk u p.val.1).map f
  let mappedPath := pOpen.map (slitBoxOpenGraphToSquareLatticeHom n A)
  let c := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  have hrange := latticePolygonOfCycle_vertex_support (slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p)
  have hv : P.vertex i ∈ Set.range c.support.get := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  rcases hv with ⟨j, hj⟩
  have hmem : P.vertex i ∈ c.support := by
    rw [← hj]
    exact List.get_mem _ _
  change -(n + 1 : ℤ) ≤ (P.vertex i).2 ∧ (P.vertex i).2 ≤ (n + 1 : ℤ)
  change P.vertex i ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support at hmem
  dsimp [slitBoxFirstHitCandidateCycle] at hmem
  have hsplit := (SimpleGraph.Walk.mem_support_append_iff _ _).mp hmem
  rcases hsplit with hpath | hreturn
  · have hpath' : P.vertex i ∈ mappedPath.support := by
      change P.vertex i ∈
        ((SimpleGraph.Walk.map (slitBoxOpenGraphToSquareLatticeHom n A)
          ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map f)).support)
      exact hpath
    have hmap : mappedPath.support = pOpen.support.map
        (slitBoxOpenGraphToSquareLatticeHom n A) :=
      SimpleGraph.Walk.support_map (f := slitBoxOpenGraphToSquareLatticeHom n A) pOpen
    rw [hmap] at hpath'
    rcases List.mem_map.mp hpath' with ⟨v, hv, hval⟩
    rw [← hval]
    have hbox := v.property
    rw [mem_latticeRectangle] at hbox
    have htop : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by push_cast; omega
    rw [htop] at hbox
    simpa [slitBoxOpenGraphToSquareLatticeHom] using (show -(n + 1 : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ n + 1 by omega)
  · have ha : u.val.1.toNat ≤ n := by
      have hbox := u.property
      rw [mem_latticeRectangle] at hbox
      have heq : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by push_cast; omega
      rw [heq] at hbox
      have hh : (u.val.1.toNat : ℤ) ≤ n := by
        rw [Int.toNat_of_nonneg huX]
        exact hbox.1.2
      exact_mod_cast hh
    have hk : p.val.1.val.2.toNat ≤ n := by
      have ht := (mem_slitBoxWiredArc_iff n p.val.1).mp p.property.1
      have hh : (p.val.1.val.2.toNat : ℤ) ≤ n := by
        rw [Int.toNat_of_nonneg ht.2.1]
        exact ht.2.2
      exact_mod_cast hh
    change P.vertex i ∈
      (slitBoxCanonicalReturnWalk n u huY huX p.val.1 p.property.1).support at hreturn
    have hrouteMem : P.vertex i ∈
        (slitBoxExteriorReturnWalkNat n u.val.1.toNat p.val.1.val.2.toNat ha hk).val.support := by
      simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.support_copy] using hreturn
    have hcoord := return_support_y_bounds n u.val.1.toNat p.val.1.val.2.toNat ha hk hrouteMem
    simpa [P, slitBoxFirstHitCandidatePolygon, latticePolygonOfCycle] using hcoord

private theorem candidate_cycle_edge_mem_of_return_edge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (edge : Sym2 LatticeVertex)
    (hedge : edge ∈ (slitBoxCanonicalReturnWalk n u huY huX p.val.1 p.property.1).edges) :
    edge ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges := by
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := horizontalStripBaseHom n A hA
  let t := p.val.1
  let r := slitBoxCanonicalReturnWalk n u huY huX t p.property.1
  let preWalk : squareLattice.Walk u.val t.val :=
    (((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A))
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX p = preWalk.append r := by rfl
  rw [hcycle, SimpleGraph.Walk.edges_append]
  exact List.mem_append.mpr (Or.inr hedge)

private theorem candidate_return_edge_boundary_bond
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (e : Medial.LatticeBond)
    (hedge : e.toSym2 ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges) :
    ∃ i : ZMod ((slitBoxFirstHitCandidateCycle n hn u huY huX p).length - 3 + 3),
      e = (slitBoxFirstHitCandidatePolygon n hn u huY huX p).boundaryBond i := by
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  have hcy := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  obtain ⟨i, hi⟩ := (latticePolygonOfCycle_edge_iff hcy e.toSym2).mp hedge
  have hEq : e.toSym2 = s(P.vertex i, P.vertex (i + 1)) := by
    simpa [P, slitBoxFirstHitCandidatePolygon] using hi
  exact ⟨i, (P.eq_boundaryBond_iff i e).mpr hEq⟩

private theorem candidate_vertex_y_bounds_all
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) :
    ∀ i : ZMod ((slitBoxFirstHitCandidateCycle n hn u huY huX p).length - 3 + 3),
      -(n + 1 : ℤ) ≤ ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).vertex i).2 ∧
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).vertex i).2 ≤ (n + 1 : ℤ) := by
  intro i
  exact candidate_vertex_y_bounds n hn u huY huX p i

private theorem candidate_right_center_exterior
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) (δ : PositiveMesh) (j : ℤ) :
    latticeCellCenter δ (j, (n + 1 : ℤ)) ∈
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).exterior δ := by
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  have hverts := candidate_vertex_y_bounds_all n hn u huY huX p
  exact P.exterior_of_im_gt_vertex_bound δ (n + 1)
    (fun i => (hverts i).2) (by simp only [latticeCellCenter]; push_cast; nlinarith [δ.property])

theorem slitBoxFirstHitCandidate_top_strip_inside
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (j : ℤ) (hlo : 0 ≤ j) (hhi : j ≤ (n : ℤ)) :
    latticeCellCenter δ (j, (n : ℤ)) ∈
      (slitBoxFirstHitCandidatePolygon n hn u huY huX p).domain δ := by
  classical
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  let e : Medial.LatticeBond := ⟨(j, (n + 1 : ℤ)), .horizontal⟩
  have hr := slitBoxCanonicalReturnWalk_top_edge_mem n u huY huX
    p.val.1 p.property.1 j hlo hhi
  have heEdge : e.toSym2 ∈
      (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges :=
    candidate_cycle_edge_mem_of_return_edge n hn u huY huX p e.toSym2 (by simpa [e, Medial.LatticeBond.toSym2, Medial.LatticeBond.source, Medial.LatticeBond.target] using hr)
  obtain ⟨i, hboundary⟩ := candidate_return_edge_boundary_bond n hn u huY huX p e heEdge
  have hdiff := (P.cellCenters_differ_iff_boundaryBond δ e).2 ⟨i, hboundary⟩
  have hout := candidate_right_center_exterior n hn u huY huX p δ j
  have hnot : latticeCellCenter δ (j, (n + 1 : ℤ)) ∉ P.domain δ := by
    intro hdom
    exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hdom hout)
  by_contra hbottom
  have heq : (latticeCellCenter δ (j, (n + 1 : ℤ)) ∈ P.domain δ) =
      (latticeCellCenter δ (j, (n : ℤ)) ∈ P.domain δ) := by
    apply propext
    constructor
    · intro hout'
      exact (hnot hout').elim
    · intro hinside
      exact (hbottom hinside).elim
  apply hdiff
  simp [e, Medial.LatticeBond.faceBase, latticeCellCenter] at heq ⊢
  ring_nf at heq ⊢
  exact heq

end PottsContinuity.FKC.FiniteFK
