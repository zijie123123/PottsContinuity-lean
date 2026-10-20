module

public import PottsContinuity.Thm3.Push.BottomCapPath
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

/-- Two distinct bottom contacts of a confined simple path close by a genuine
cap below y=0. All negative-height vertices stay between its endpoint columns,
and every original-square edge remains on the original path. -/
theorem exists_bottom_capped_cycle (N : ℕ) (x y : ℤ) (hxy : x ≠ y)
    (p : PD.FK.squareLattice.Walk (x,0) (y,0)) (hp : p.IsPath)
    (hinside : ∀ z ∈ p.support, z ∈ latticeRectangle (0,0) N N) :
    ∃ c : PD.FK.squareLattice.Walk (x,0) (x,0),
      c.IsCycle ∧ p.edges ⊆ c.edges ∧
      (∀ z ∈ c.support, 0 ≤ z.1 ∧ z.1 ≤ (N : ℤ)) ∧
      (∀ z ∈ c.support, z.2 < 0 → min x y ≤ z.1 ∧ z.1 ≤ max x y) ∧
      ∀ a b : LatticeVertex, 0 ≤ a.2 → 0 ≤ b.2 →
        s(a,b) ∈ c.edges → s(a,b) ∈ p.edges := by
  obtain ⟨q,hq,hqlen,hqs,hqbottom,hqedges⟩ := exists_bottom_cap_path y x (Ne.symm hxy)
  have hx := (mem_latticeRectangle (0,0) (x,0) N N).mp (hinside _ p.start_mem_support)
  have hy := (mem_latticeRectangle (0,0) (y,0) N N).mp (hinside _ p.end_mem_support)
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzp hzq
    have hzP := List.mem_of_mem_tail hzp
    have hzQ := List.mem_of_mem_tail hzq
    have hzbox := (mem_latticeRectangle (0,0) z N N).mp (hinside z hzP)
    rcases hqbottom z hzQ (by dsimp at hzbox; omega) with rfl | rfl
    · exact path_start_not_mem_tail q hq hzq
    · exact path_start_not_mem_tail p hp hzp
  let c := p.append q
  refine ⟨c,hp.isCycle_append hq hdisj (Or.inr hqlen),?_,?_,?_,?_⟩
  · intro e he
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ he
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := (mem_latticeRectangle (0,0) z N N).mp (hinside z hz)
      dsimp at hh
      exact ⟨by omega,by omega⟩
    · have hh := hqs z hz
      dsimp at hx hy
      exact ⟨by omega,by omega⟩
  · intro z hz hz0
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := (mem_latticeRectangle (0,0) z N N).mp (hinside z hz)
      dsimp at hh
      omega
    · have hh := hqs z hz
      exact ⟨by omega,by omega⟩
  · intro a b ha hb he
    rw [SimpleGraph.Walk.edges_append,List.mem_append] at he
    rcases he with he | he
    · exact he
    · exact (hqedges a b ha hb he).elim

end PottsContinuity.Push
