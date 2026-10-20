module

public import PottsContinuity.Critical.PeierlsLow
public import PottsContinuity.PD.RCInfinite.ExteriorBranches
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Critical

open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- Every infinite component in a locally finite graph contains simple paths
of every prescribed finite length starting at its root. -/
theorem exists_path_of_infinite_component {V : Type*} :
    ∀ (G : SimpleGraph V) (x : V) (n : ℕ),
      (∀ v, (G.neighborSet v).Finite) →
      {y | G.Reachable x y}.Infinite →
      ∃ y, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n := by
  intro G x n
  induction n generalizing G x with
  | zero =>
      intro hN hinf
      exact ⟨x, SimpleGraph.Walk.nil, by simp, by simp⟩
  | succ n ih =>
      intro hN hinf
      obtain ⟨z, hxz, hzinf⟩ :=
        infinite_component_has_infinite_deleted_neighbor G x (hN x) hinf
      let H := G.deleteIncidenceSet x
      have hHN : ∀ v, (H.neighborSet v).Finite := by
        intro v
        apply (hN v).subset
        intro w hw
        change H.Adj v w at hw
        exact SimpleGraph.deleteIncidenceSet_le G x hw
      obtain ⟨y, q, hq, hqLen⟩ := ih H z hHN hzinf
      let qG : G.Walk z y := q.transfer G fun e he =>
        SimpleGraph.edgeSet_mono (SimpleGraph.deleteIncidenceSet_le G x)
          (q.edges_subset_edgeSet he)
      have hxNotQ : x ∉ q.support := by
        by_cases hnil : q.Nil
        · have hzx : x ≠ z := hxz.ne
          rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil]
          simp [hzx]
        · intro hxq
          have hxmem : x ∈ H.support :=
            H.mem_support_of_mem_walk_support q hnil hxq
          have hsub := SimpleGraph.support_deleteIncidenceSet_subset G x hxmem
          exact hsub.2 (by simp)
      have hqG : qG.IsPath := by
        exact hq.transfer (fun e he =>
          SimpleGraph.edgeSet_mono (SimpleGraph.deleteIncidenceSet_le G x)
            (q.edges_subset_edgeSet he))
      have havoid : x ∉ qG.support := by
        simpa [qG, SimpleGraph.Walk.support_transfer] using hxNotQ
      let p : G.Walk x y := SimpleGraph.Walk.cons hxz qG
      refine ⟨y, p, ?_, ?_⟩
      · simpa [p] using
          (SimpleGraph.Walk.cons_isPath_iff hxz qG).2 ⟨hqG, havoid⟩
      · simp [p, qG, hqLen]

/-- An infinite open cluster at the origin forces a simple open walk of every
finite length. -/
theorem infiniteAt_subset_openSimpleWalkEvent (n : ℕ) :
    infiniteAt (0, 0) ⊆
      {ω : LatticeConfiguration | (fun e => ω e = true) ∈ openSimpleWalkEvent (0, 0) n} := by
  intro ω hω
  have hloc (v : LatticeVertex) :
      ((PottsContinuity.PD.rcInfiniteOpenGraph ω).neighborSet v).Finite := by
    have hsub : (PottsContinuity.PD.rcInfiniteOpenGraph ω).neighborSet v ⊆
        squareLattice.neighborSet v := by
      intro w hw
      change (PottsContinuity.PD.rcInfiniteOpenGraph ω).Adj v w at hw
      obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω v w).mp hw
      exact squareLattice.mem_edgeSet.mp he
    exact (squareLattice_neighborSet_finite v).subset hsub
  obtain ⟨y, p, hp, hlen⟩ := exists_path_of_infinite_component
    (PottsContinuity.PD.rcInfiniteOpenGraph ω) (0, 0) n hloc hω
  have hOpen : PottsContinuity.PD.rcInfiniteOpenGraph ω ≤ squareLattice := by
    intro u v huv
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω u v).mp huv
    exact squareLattice.mem_edgeSet.mp he
  let pBase : squareLattice.Walk (0, 0) y := p.mapLe hOpen
  have hpBase : pBase.IsPath := hp.mapLe hOpen
  change ∃ y, ∃ p : squareLattice.Walk (0, 0) y,
    p.IsPath ∧ p.length = n ∧ (fun e => ω e = true) ∈ walkOpenEvent p
  refine ⟨y, pBase, hpBase, ?_, ?_⟩
  · simpa [pBase] using hlen
  · intro e he
    have heOpen : e.val ∈ p.edges := by simpa [pBase] using he
    have heGraph : e.val ∈ (PottsContinuity.PD.rcInfiniteOpenGraph ω).edgeSet :=
      p.edges_subset_edgeSet heOpen
    obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
    have hEdge : s(u, v) ∈ (PottsContinuity.PD.rcInfiniteOpenGraph ω).edgeSet := by
      exact Eq.mp (congrArg (fun z : Sym2 LatticeVertex =>
        z ∈ (PottsContinuity.PD.rcInfiniteOpenGraph ω).edgeSet) huv.symm) heGraph
    have hAdj : (PottsContinuity.PD.rcInfiniteOpenGraph ω).Adj u v :=
      (PottsContinuity.PD.rcInfiniteOpenGraph ω).mem_edgeSet.mp hEdge
    obtain ⟨hsquare, hopen⟩ := (rcInfiniteOpenGraph_adj ω u v).mp hAdj
    have heq : e = ⟨s(u, v), hsquare⟩ := Subtype.ext huv.symm
    change ω e = true
    rw [heq]
    exact hopen

end
end PottsContinuity.Critical
