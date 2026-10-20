-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCellConnectivity.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundaryParity
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryInjective
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryGraphFaithfulness
public import PottsContinuity.FKC.Domains.LatticeCellComponentBoundary
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import PottsContinuity.FKC.Medial.FiniteEvenSubgraphOfCycle
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- An even subgraph under a finite simple cycle is empty or the whole cycle,
without requiring the ambient vertex type itself to be finite. -/
theorem evenSubgraphOfCycle_eq_bot_or_cycle_of_finite_support
    {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (H : SimpleGraph V)
    (hsub : H ≤ p.toSubgraph.spanningCoe)
    (heven : ∀ v : V, Even (H.neighborSet v).ncard) :
    H = ⊥ ∨ H = p.toSubgraph.spanningCoe := by
  classical
  let C := p.toSubgraph.spanningCoe
  have hneighborC (v : V) : C.neighborSet v = p.toSubgraph.neighborSet v := by
    ext w
    rfl
  have hfull_of_neighbor (v : V) (hv : v ∈ p.support)
      (hnon : (H.neighborSet v).Nonempty) :
      H.neighborSet v = C.neighborSet v := by
    have hsubN : H.neighborSet v ⊆ C.neighborSet v := SimpleGraph.neighborSet_mono hsub v
    have hCcard : (C.neighborSet v).ncard = 2 := by
      rw [hneighborC]
      exact hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hCpos : 0 < (C.neighborSet v).ncard := by rw [hCcard]; omega
    have hCfinite : (C.neighborSet v).Finite := Set.finite_of_ncard_pos hCpos
    have hle : (H.neighborSet v).ncard ≤ 2 := by
      calc
        (H.neighborSet v).ncard ≤ (C.neighborSet v).ncard := Set.ncard_le_ncard hsubN hCfinite
        _ = 2 := hCcard
    have hfinite : (H.neighborSet v).Finite := hCfinite.subset hsubN
    have hpos : 0 < (H.neighborSet v).ncard := (Set.ncard_pos hfinite).mpr hnon
    have hHcard : (H.neighborSet v).ncard = 2 := by
      obtain ⟨k, hk⟩ := heven v
      omega
    apply Set.eq_of_subset_of_ncard_le hsubN ?_ hCfinite
    rw [hCcard, hHcard]
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  · obtain ⟨a, b, hab⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hbot
    have habC : C.Adj a b := hsub hab
    have haV : a ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert habC
    have haSupport : a ∈ p.support := p.mem_verts_toSubgraph.mp haV
    have hstart : H.neighborSet a = C.neighborSet a :=
      hfull_of_neighbor a haSupport ⟨b, (H.mem_neighborSet a b).mpr hab⟩
    have hprop : ∀ {x y : p.toSubgraph.verts}
        (w : p.toSubgraph.coe.Walk x y),
        H.neighborSet x.1 = C.neighborSet x.1 →
          H.neighborSet y.1 = C.neighborSet y.1 := by
      intro x y w
      induction w with
      | nil => intro hx; exact hx
      | @cons x y z hadj tail ih =>
          intro hx
          have hadjC : C.Adj x.1 y.1 := hadj
          have hyC : y.1 ∈ C.neighborSet x.1 := (C.mem_neighborSet x.1 y.1).mpr hadjC
          have hyH : y.1 ∈ H.neighborSet x.1 := by simpa [hx] using hyC
          have hadjH : H.Adj x.1 y.1 := (H.mem_neighborSet x.1 y.1).mp hyH
          have hxH : x.1 ∈ H.neighborSet y.1 :=
            (H.mem_neighborSet y.1 x.1).mpr hadjH.symm
          have hySupport : y.1 ∈ p.support := p.mem_verts_toSubgraph.mp y.2
          have hnext : H.neighborSet y.1 = C.neighborSet y.1 :=
            hfull_of_neighbor y.1 hySupport ⟨x.1, hxH⟩
          exact ih hnext
    have hfull : ∀ v : V, v ∈ p.support →
        H.neighborSet v = C.neighborSet v := by
      intro v hv
      let av : p.toSubgraph.verts := ⟨a, haV⟩
      let vv : p.toSubgraph.verts := ⟨v, p.mem_verts_toSubgraph.mpr hv⟩
      have hreach : p.toSubgraph.coe.Reachable av vv := p.toSubgraph_connected av vv
      rcases hreach with ⟨w⟩
      exact hprop w hstart
    apply Or.inr
    apply le_antisymm hsub
    intro x y hxy
    have hxV : x ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hxy
    have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxV
    have hfullx := hfull x hxSupport
    have hyC : y ∈ C.neighborSet x := (C.mem_neighborSet x y).mpr hxy
    have hyH : y ∈ H.neighborSet x := by simpa [hfullx] using hyC
    exact (H.mem_neighborSet x y).mp hyH

end PottsContinuity.FKC.Medial

namespace PottsContinuity.FKC.LatticePolygon

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

noncomputable section

theorem interiorCellBases_connected_of_cycle
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (δ : PositiveMesh) :
    (squareLattice.induce
      (↑((latticePolygonOfCycle hp).interiorCellBases δ) : Set LatticeVertex)).Connected := by
  classical
  let P := latticePolygonOfCycle hp
  let S := P.interiorCellBases δ
  have hcycle : latticeCellBoundaryGraph S = p.toSubgraph.spanningCoe := by
    simpa [P, S] using latticeCellBoundaryGraph_interiorCellBases_eq_cycle hp δ
  have hpne : p.toSubgraph.spanningCoe ≠ (⊥ : SimpleGraph LatticeVertex) := by
    intro hbot
    have hcard := hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
    have hAdj : p.toSubgraph.neighborSet v = ∅ := by
      ext w
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hadj
      have hspan : p.toSubgraph.spanningCoe.Adj v w := hadj
      rw [hbot] at hspan
      exact hspan
    rw [hAdj] at hcard
    simp at hcard
  have hSboundary : latticeCellBoundaryGraph S ≠ (⊥ : SimpleGraph LatticeVertex) := by
    rw [hcycle]
    exact hpne
  obtain ⟨a,b,hab⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hSboundary
  have hface := (latticeCellBoundaryGraph_adj_iff S a b).mp hab
  obtain ⟨e, heq, hdiff⟩ := hface.2
  have hSnonempty : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : e ∈ latticeCellBoundaryBonds S :=
      (mem_latticeCellBoundaryBonds S e).mpr hdiff
    rw [hzero, mem_latticeCellBoundaryBonds] at this
    simp at this
  obtain ⟨c,hc⟩ := hSnonempty
  let T := PottsContinuity.FKC.Domains.latticeCellReachableComponent S c hc
  have hTnonempty : T.Nonempty := ⟨c, PottsContinuity.FKC.Domains.mem_latticeCellReachableComponent_self S c hc⟩
  have hTBonds : latticeCellBoundaryBonds T ⊆ latticeCellBoundaryBonds S :=
    PottsContinuity.FKC.Domains.latticeCellBoundaryBonds_reachableComponent_subset S c hc
  have hTle : latticeCellBoundaryGraph T ≤ p.toSubgraph.spanningCoe := by
    rw [← hcycle]
    exact (latticeCellBoundaryGraph_le_iff T S).2 hTBonds
  have hTeven : ∀ x : LatticeVertex, Even ((latticeCellBoundaryGraph T).neighborSet x).ncard :=
    latticeCellBoundaryGraph_even_degree T
  have hTnotbot : latticeCellBoundaryGraph T ≠ (⊥ : SimpleGraph LatticeVertex) := by
    intro hbot
    have hbonds : latticeCellBoundaryBonds T = latticeCellBoundaryBonds (∅ : Finset LatticeVertex) := by
      apply (latticeCellBoundaryGraph_eq_iff T ∅).mp
      rw [hbot, latticeCellBoundaryGraph_empty]
    have hTempty : T = ∅ := latticeCellBoundaryBonds_injective hbonds
    obtain ⟨x,hx⟩ := hTnonempty
    rw [hTempty] at hx
    simp at hx
  have hcyclecase := evenSubgraphOfCycle_eq_bot_or_cycle_of_finite_support p hp
    (latticeCellBoundaryGraph T) hTle hTeven
  have hTcycle : latticeCellBoundaryGraph T = p.toSubgraph.spanningCoe := by
    rcases hcyclecase with hbot | hfull
    · exact (hTnotbot hbot).elim
    · exact hfull
  have hTboundaries : latticeCellBoundaryBonds T = latticeCellBoundaryBonds S := by
    apply Finset.Subset.antisymm
    · exact hTBonds
    · apply (latticeCellBoundaryGraph_le_iff S T).mp
      rw [hcycle, ← hTcycle]
  have hTS : T = S := latticeCellBoundaryBonds_injective hTboundaries
  let : Nonempty {x : LatticeVertex // x ∈ S} := ⟨⟨c,hc⟩⟩
  refine ⟨?_⟩
  intro a b
  have hca : a.val ∈ T := by simp [hTS]
  have hcb : b.val ∈ T := by simp [hTS]
  obtain ⟨_, ⟨ha', hreach⟩⟩ := Finset.mem_filter.mp hca
  obtain ⟨_, ⟨hb', hreachb⟩⟩ := Finset.mem_filter.mp hcb
  simpa using hreach.symm.trans hreachb

end
end PottsContinuity.FKC.LatticePolygon
