module

public import PottsContinuity.Thm3.RSW.SlitRayIndex
public import PottsContinuity.Thm3.RSW.SlitCrosscutHit
public import PottsContinuity.Thm3.RSW.SlitTipPositive
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarTopology
noncomputable section

/-- The first marked-ray contact of the disjoint earlier source walk is
approached from the LEFT, at the same height strictly above the tip. -/
theorem first_markedRay_contact_approaches_left
    (a b B t x y H : ℤ) (hab : a < b)
    (p : squareLattice.Walk (a,0) (B,t))
    (q : squareLattice.Walk (b,0) (x,y))
    (hp : ∀ w ∈ p.support, 0 ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ H)
    (hq : ∀ w ∈ q.support, x ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ H)
    (hdis : ∀ w ∈ p.support, w ∉ q.support)
    (m : ℕ) (hmpos : 0 < m) (hmle : m ≤ p.length)
    (hmhit : (p.getVert m).1 = x ∧ y ≤ (p.getVert m).2)
    (hmfirst : ∀ j : ℕ, j < m → ¬ ((p.getVert j).1 = x ∧ y ≤ (p.getVert j).2)) :
    (p.getVert (m-1)).1 = x-1 ∧
      (p.getVert (m-1)).2 = (p.getVert m).2 ∧ y < (p.getVert (m-1)).2 := by
  have hmark : (x,(p.getVert m).2) ∉ q.support := by
    have he : p.getVert m = (x,(p.getVert m).2) := Prod.ext hmhit.1 rfl
    rw [← he]
    exact hdis _ (p.getVert_mem_support m)
  have hyz : y < (p.getVert m).2 := by
    by_contra h
    have he : (x,(p.getVert m).2) = (x,y) := by
      apply Prod.ext
      · rfl
      · dsimp; omega
    exact hmark (he.symm ▸ q.end_mem_support)
  have he : m-1+1 = m := by omega
  have hadj := p.adj_getVert_succ (i := m-1) (by omega)
  rw [he,squareLattice_adj_iff] at hadj
  have hprev := hmfirst (m-1) (by omega)
  have hcases :
      ((p.getVert (m-1)).1 = x-1 ∧ (p.getVert (m-1)).2 = (p.getVert m).2) ∨
      ((p.getVert (m-1)).1 = x+1 ∧ (p.getVert (m-1)).2 = (p.getVert m).2) := by
    rcases hadj with ⟨h | h,hy⟩ | ⟨hx,h | h⟩
    · exact Or.inl ⟨by omega,hy⟩
    · exact Or.inr ⟨by omega,hy⟩
    · exact (hprev ⟨by omega,by omega⟩).elim
    · exact (hprev ⟨by omega,by omega⟩).elim
  rcases hcases with hleft | hright
  · exact ⟨hleft.1,hleft.2,by omega⟩
  obtain ⟨C,hC,hCs,hCz⟩ := exists_slit_tip_loop_with_ray_indices a b B x y H
    (p.getVert m).2 hab hyz (hp _ (p.getVert_mem_support m)).2.2.2 q hq hmark
  have havoid : ∀ w ∈ (p.take (m-1)).support, w ∉ C.support := by
    intro w hw hloop
    have hwp := (p.isSubwalk_take (m-1)).support_subset hw
    have hwb := hp w hwp
    obtain ⟨j,hj,_⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    rw [SimpleGraph.Walk.take_getVert] at hj
    have hnotray : ¬ (w.1 = x ∧ y ≤ w.2) := by
      exact hj ▸ hmfirst (min (m-1) j) (by have := Nat.min_le_left (m-1) j; omega)
    rcases hC w hloop with hqmem | hray | htop | hright | hlow
    · exact hdis w hwp hqmem
    · exact hnotray hray
    · omega
    · omega
    · omega
  have hidx := rayIndex_eq_of_disjoint_support C (p.take (m-1)) havoid
  have huEq : p.getVert (m-1) = (x+1,(p.getVert m).2) := Prod.ext hright.1 hright.2
  rw [huEq,hCs,hCz] at hidx
  norm_num at hidx

end
end PottsContinuity.RSW
