-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateExteriorNeighbors.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateRightStrip
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

private theorem verticalReturn_outside_incident_edge_eq_top
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    {z y : LatticeVertex} (hz : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n))
    (he : s(z,y) ∈ (slitReturnVerticalUpWalk 0 (k : ℤ) (n + 1 - k)).edges) :
    s(z,y) = s(((0 : ℤ), (n : ℤ)), ((0 : ℤ), (n + 1 : ℤ))) := by
  have hzSup := (slitReturnVerticalUpWalk 0 (k : ℤ) (n+1-k)).fst_mem_support_of_mem_edges he
  have hySup := (slitReturnVerticalUpWalk 0 (k : ℤ) (n+1-k)).snd_mem_support_of_mem_edges he
  obtain ⟨hzx,hzlo,hzhi⟩ := slitReturnVerticalUpWalk_support_bounds 0 (k : ℤ) (n+1-k) hzSup
  obtain ⟨hyx,hylo,hyhi⟩ := slitReturnVerticalUpWalk_support_bounds 0 (k : ℤ) (n+1-k) hySup
  have hzY : z.2 = (n + 1 : ℤ) := by
    by_contra h
    have hbox : z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
      rw [mem_latticeRectangle]
      push_cast
      constructor
      · constructor <;> omega
      · constructor <;> omega
    exact hz hbox
  have hadj : squareLattice.Adj z y :=
    squareLattice.mem_edgeSet.mp
      ((slitReturnVerticalUpWalk 0 (k : ℤ) (n+1-k)).edges_subset_edgeSet he)
  have hcoords := (squareLattice_adj_iff z y).mp hadj
  have hyY : y.2 = n := by
    rcases hcoords with ⟨⟨hxy | hyx, hsame⟩⟩ | ⟨hsame, hstep | hstep⟩ <;> omega
  have hzEq : z = ((0 : ℤ), (n + 1 : ℤ)) := by
    exact Prod.ext hzx hzY
  have hyEq : y = ((0 : ℤ), (n : ℤ)) := by
    exact Prod.ext hyx hyY
  rw [hzEq, hyEq]
  simp [Sym2.eq_swap]

private theorem verticalReturn_top_edge_mem (n k : ℕ) (hk : k ≤ n) :
    s(((0 : ℤ), (n : ℤ)), ((0 : ℤ), (n + 1 : ℤ))) ∈
      (slitReturnVerticalUpWalk 0 (k : ℤ) (n + 1 - k)).edges := by
  exact slitReturnVerticalUpWalk_edge_mem 0 (k : ℤ) (n + 1 - k) n (by omega) (by omega)

private theorem exteriorReturn_incident_edges_eq
    (n a k l : ℕ) (hn : 1 ≤ n) (ha : a ≤ n) (hk : k ≤ n) (hl : l ≤ n)
    {z y : LatticeVertex}
    (hz : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) :
    (s(z,y) ∈ (slitBoxExteriorReturnWalkNat n a k ha hk).val.edges) ↔
      s(z,y) ∈ (slitBoxExteriorReturnWalkNat n a l ha hl).val.edges := by
  have hvk : s(z,y) ∈ (slitReturnVerticalUpWalk 0 (k : ℤ) (n+1-k)).edges ↔
      s(z,y) ∈ (slitReturnVerticalUpWalk 0 (l : ℤ) (n+1-l)).edges := by
    constructor
    · intro he
      rw [verticalReturn_outside_incident_edge_eq_top n k hn hk hz he]
      exact verticalReturn_top_edge_mem n l hl
    · intro he
      rw [verticalReturn_outside_incident_edge_eq_top n l hn hl hz he]
      exact verticalReturn_top_edge_mem n k hk
  simp only [slitBoxExteriorReturnWalkNat, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
    List.mem_append, List.mem_reverse]
  constructor
  · intro h
    rcases h with h | h | h | h | h
    · exact Or.inl (hvk.mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · intro h
    rcases h with h | h | h | h | h
    · exact Or.inl (hvk.mpr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

def candidateAllOpenHom (n : ℕ)
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

private theorem cycleNeighborSet_eq_walkEdges
    {z : LatticeVertex} (c : squareLattice.Walk z z) (x : LatticeVertex) :
    c.toSubgraph.spanningCoe.neighborSet x = {y | s(x,y) ∈ c.edges} := by
  ext y
  change c.toSubgraph.Adj x y ↔ s(x,y) ∈ c.edges
  rw [← SimpleGraph.Subgraph.mem_edgeSet]
  exact SimpleGraph.Walk.mem_edges_toSubgraph c

/-- Two actual candidate cycles have identical neighbor sets at every vertex
outside the literal slit box. -/
theorem slitBoxFirstHitCandidateCycle_neighborSet_eq_of_outside
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p q : SlitBoxFirstHitBaseCandidates n u) {z : LatticeVertex}
    (hz : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) :
    (slitBoxFirstHitCandidateCycle n hn u huY huX p).toSubgraph.spanningCoe.neighborSet z =
      (slitBoxFirstHitCandidateCycle n hn u huY huX q).toSubgraph.spanningCoe.neighborSet z := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let f := candidateAllOpenHom n A rfl
  let hpfx := (((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map f).map
    (slitBoxOpenGraphToSquareLatticeHom n A))
  let hqfx := (((q.val.2 : (slitBoxGraph n).Walk u q.val.1).map f).map
    (slitBoxOpenGraphToSquareLatticeHom n A))
  let rp := slitBoxCanonicalReturnWalk n u huY huX p.val.1 p.property.1
  let rq := slitBoxCanonicalReturnWalk n u huY huX q.val.1 q.property.1
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  have hcp : cp = hpfx.append rp := by
    dsimp [cp, hpfx, rp, slitBoxFirstHitCandidateCycle]
    rfl
  have hcq : cq = hqfx.append rq := by
    dsimp [cq, hqfx, rq, slitBoxFirstHitCandidateCycle]
    rfl
  have hpfx_box : ∀ x ∈ hpfx.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨v,hv,rfl⟩
    rw [SimpleGraph.Walk.support_map] at hv
    rcases List.mem_map.mp hv with ⟨w,hw,rfl⟩
    simp
  have hqfx_box : ∀ x ∈ hqfx.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨v,hv,rfl⟩
    rw [SimpleGraph.Walk.support_map] at hv
    rcases List.mem_map.mp hv with ⟨w,hw,rfl⟩
    simp
  have hpfx_no_edge (y : LatticeVertex) : s(z,y) ∉ hpfx.edges := by
    intro he
    exact hz (hpfx_box z (hpfx.fst_mem_support_of_mem_edges he))
  have hqfx_no_edge (y : LatticeVertex) : s(z,y) ∉ hqfx.edges := by
    intro he
    exact hz (hqfx_box z (hqfx.fst_mem_support_of_mem_edges he))
  have ha : u.val.1.toNat ≤ n := by
    have hbox := u.property
    rw [mem_latticeRectangle] at hbox
    have htop : -(n : ℤ) + (2*n : ℕ) = (n : ℤ) := by push_cast; omega
    rw [htop] at hbox
    have hxcast : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg huX]
      exact hbox.1.2
    exact_mod_cast hxcast
  have hpArc := (mem_slitBoxWiredArc_iff n p.val.1).mp p.property.1
  have hqArc := (mem_slitBoxWiredArc_iff n q.val.1).mp q.property.1
  have hk : p.val.1.val.2.toNat ≤ n := by
    have hh : (p.val.1.val.2.toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg hpArc.2.1]
      exact hpArc.2.2
    exact_mod_cast hh
  have hl : q.val.1.val.2.toNat ≤ n := by
    have hh : (q.val.1.val.2.toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg hqArc.2.1]
      exact hqArc.2.2
    exact_mod_cast hh
  have hreturns : ∀ y, s(z,y) ∈ rp.edges ↔ s(z,y) ∈ rq.edges := by
    intro y
    simpa [rp, rq, slitBoxCanonicalReturnWalk, SimpleGraph.Walk.edges_copy] using
      (exteriorReturn_incident_edges_eq n u.val.1.toNat p.val.1.val.2.toNat
        q.val.1.val.2.toNat hn ha hk hl hz (z := z) (y := y))
  have hedgeiff (y : LatticeVertex) : s(z,y) ∈ cp.edges ↔ s(z,y) ∈ cq.edges := by
    change s(z,y) ∈ (hpfx.append rp).edges ↔ s(z,y) ∈ (hqfx.append rq).edges
    have hpEdges := SimpleGraph.Walk.edges_append hpfx rp
    have hqEdges := SimpleGraph.Walk.edges_append hqfx rq
    rw [hpEdges, hqEdges, List.mem_append, List.mem_append]
    constructor
    · rintro (hprefix | hreturn)
      · exact (hpfx_no_edge y hprefix).elim
      · exact Or.inr ((hreturns y).mp hreturn)
    · rintro (hprefix | hreturn)
      · exact (hqfx_no_edge y hprefix).elim
      · exact Or.inr ((hreturns y).mpr hreturn)
  change cp.toSubgraph.spanningCoe.neighborSet z =
    cq.toSubgraph.spanningCoe.neighborSet z
  rw [cycleNeighborSet_eq_walkEdges cp z, cycleNeighborSet_eq_walkEdges cq z]
  ext y
  exact hedgeiff y

/-- Outside the literal box, the union of two candidate cycle graphs has
degree two at every vertex of the first cycle. -/
theorem slitBoxFirstHitCandidateCycle_union_degree_two_of_outside
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p q : SlitBoxFirstHitBaseCandidates n u) {z : LatticeVertex}
    (hz : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n))
    (hzp : z ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support) :
    (((slitBoxFirstHitCandidateCycle n hn u huY huX p).toSubgraph.spanningCoe ⊔
      (slitBoxFirstHitCandidateCycle n hn u huY huX q).toSubgraph.spanningCoe).neighborSet z).ncard = 2 := by
  classical
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  have hneighbors := slitBoxFirstHitCandidateCycle_neighborSet_eq_of_outside
    n hn u huY huX p q hz
  have hneighbors' : cp.toSubgraph.spanningCoe.neighborSet z =
      cq.toSubgraph.spanningCoe.neighborSet z := by simpa [cp, cq] using hneighbors
  have hunion : (cp.toSubgraph.spanningCoe ⊔ cq.toSubgraph.spanningCoe).neighborSet z =
      cp.toSubgraph.spanningCoe.neighborSet z := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]
    rw [← cp.toSubgraph.spanningCoe.mem_neighborSet, ← cq.toSubgraph.spanningCoe.mem_neighborSet,
      hneighbors']
    simp
  rw [hunion]
  have hcyc : cp.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  have hzp' : z ∈ cp.support := by simpa [cp] using hzp
  change (cp.toSubgraph.neighborSet z).ncard = 2
  exact hcyc.ncard_neighborSet_toSubgraph_eq_two hzp'
end PottsContinuity.FKC.FiniteFK
