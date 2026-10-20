module

public import PottsContinuity.PlanarTopology.BottomSpan
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PlanarTopology
noncomputable section

/-- A bottom return enclosing the start of a bottom-to-right walk meets it.
The auxiliary exterior cap cannot introduce an intersection inside the box. -/
theorem bottom_right_walk_meets_bottom_return
    (a b B t x : ℤ) (hxa : x ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (p : squareLattice.Walk (a,0) (B,t))
    (q : squareLattice.Walk (b,0) (x,0))
    (hp : ∀ z ∈ p.support, 0 ≤ z.2)
    (hq : ∀ z ∈ q.support, z.1 ≤ B ∧ 0 ≤ z.2) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  have ht : 0 ≤ t := hp (B,t) p.end_mem_support
  obtain ⟨R,hR⟩ := vertical_walk_between (B+1) t 0
  have hadj : squareLattice.Adj (B,t) (B+1,t) := by
    rw [squareLattice_adj_iff]; dsimp; omega
  let P := p.append (hadj.toWalk.append R)
  have hP : ∀ z ∈ P.support, z ∈ p.support ∨ z.1 = B+1 := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · exact Or.inl hz
    · have he : z = (B,t) ∨ z = (B+1,t) := by simpa using hz
      rcases he with rfl | rfl
      · exact Or.inl p.end_mem_support
      · exact Or.inr rfl
    · exact Or.inr (hR z hz).1
  have hPnonneg : ∀ z ∈ P.support, 0 ≤ z.2 := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz
    · exact hp z hz
    · have he : z = (B,t) ∨ z = (B+1,t) := by simpa using hz
      rcases he with rfl | rfl <;> exact ht
    · have hh := (hR z hz).2.1
      simpa only [min_eq_right ht] using hh
  obtain ⟨z,hzq,hzp⟩ := band_interlaced_walks_intersect 0 q.reverse P
    rfl rfl rfl rfl hxa hab (by dsimp; omega)
    (by intro z hz; exact (hq z (by simpa only [SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hz)).2) hPnonneg
  have hzq' : z ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hzq
  rcases hP z hzp with hzp | hzp
  · exact ⟨z,hzp,hzq'⟩
  · have hh := (hq z hzq').1
    omega

/-- In the disjoint Case2 geometry the slit tip has strictly positive height.
A zero-height tip would create interlacing bottom contacts. -/
theorem disjoint_bottom_right_walk_tip_pos
    (a b B t x y : ℤ) (hxa : x ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (p : squareLattice.Walk (a,0) (B,t))
    (q : squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.2)
    (hq : ∀ z ∈ q.support, z.1 ≤ B ∧ 0 ≤ z.2)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) : 0 < y := by
  have hy : 0 ≤ y := (hq (x,y) q.end_mem_support).2
  by_contra h
  have hy0 : y = 0 := by omega
  subst y
  obtain ⟨z,hzp,hzq⟩ := bottom_right_walk_meets_bottom_return a b B t x
    hxa hab hbB p q hp hq
  exact hdis z hzp hzq

end
end PottsContinuity.RSW
