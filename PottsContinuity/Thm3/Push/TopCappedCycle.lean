module

public import PottsContinuity.Thm3.Push.TopCapPath
public import PottsContinuity.PD.Duality.Rectangle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

private theorem path_start_not_mem_tail {G : SimpleGraph LatticeVertex}
    {u v : LatticeVertex} (p : G.Walk u v) (hp : p.IsPath) : u ∉ p.support.tail := by
  have hn : (u :: p.support.tail).Nodup := by
    rw [SimpleGraph.Walk.cons_tail_support]
    exact hp.support_nodup
  exact (List.nodup_cons.mp hn).1

/-- A simple path in the square joining DISTINCT top vertices closes to a
simple cycle by a cap above the square. Every bond of the cycle whose endpoints
are at height at most N already belongs to the original confined path. -/
theorem exists_top_capped_cycle (N : ℕ) (x y : ℤ) (hxy : x ≠ y)
    (p : PD.FK.squareLattice.Walk (x,(N : ℤ)) (y,(N : ℤ))) (hp : p.IsPath)
    (hinside : ∀ z ∈ p.support, z ∈ latticeRectangle (0,0) N N) :
    ∃ c : PD.FK.squareLattice.Walk (x,(N : ℤ)) (x,(N : ℤ)),
      c.IsCycle ∧ p.edges ⊆ c.edges ∧
      (∀ z ∈ c.support, 0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2) ∧
      ∀ a b : LatticeVertex, a.2 ≤ (N : ℤ) → b.2 ≤ (N : ℤ) →
        s(a,b) ∈ c.edges → s(a,b) ∈ p.edges := by
  obtain ⟨q,hq,hqlen,hqs,hqtop,hqedges⟩ := exists_top_cap_path N y x (Ne.symm hxy)
  have hx := (mem_latticeRectangle (0,0) (x,(N : ℤ)) N N).mp (hinside _ p.start_mem_support)
  have hy := (mem_latticeRectangle (0,0) (y,(N : ℤ)) N N).mp (hinside _ p.end_mem_support)
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzp hzq
    have hzP := List.mem_of_mem_tail hzp
    have hzQ := List.mem_of_mem_tail hzq
    have hzbox := (mem_latticeRectangle (0,0) z N N).mp (hinside z hzP)
    rcases hqtop z hzQ (by omega) with rfl | rfl
    · exact path_start_not_mem_tail q hq hzq
    · exact path_start_not_mem_tail p hp hzp
  let c := p.append q
  refine ⟨c,hp.isCycle_append hq hdisj (Or.inr hqlen),?_,?_,?_⟩
  · intro e he
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := (mem_latticeRectangle (0,0) z N N).mp (hinside z hz)
      dsimp at hh
      exact ⟨by omega,by omega,by omega⟩
    · have hh := hqs z hz
      dsimp at hx hy
      exact ⟨by omega,by omega,by omega⟩
  · intro a b ha hb he
    rw [SimpleGraph.Walk.edges_append,List.mem_append] at he
    rcases he with he | he
    · exact he
    · exact (hqedges a b ha hb he).elim

end PottsContinuity.Push
