module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PlanarTopology.InterlacedPaths
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Horizontal steps to the left of the marked ray do not affect its
endpoint telescoping formula. -/
theorem rayIndex_telescope_of_left_horizontal (v : LatticeVertex)
    {u w : LatticeVertex} (p : PD.squareLattice.Walk u w)
    (hp : ∀ a b, s(a,b) ∈ p.edges → a.1 < v.1 → a.2 = b.2) :
    rayIndex v p = (if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0) := by
  induction p with
  | nil => simp [rayIndex]
  | @cons u z w hadj p ih =>
    have ht : ∀ a b, s(a,b) ∈ p.edges → a.1 < v.1 → a.2 = b.2 := by
      intro a b he
      exact hp a b (List.mem_cons.mpr (Or.inr he))
    have hstep : rayStep v u z = (if u.2 < v.2 then 1 else 0) - (if z.2 < v.2 then 1 else 0) := by
      by_cases hu : v.1 ≤ u.1
      · simp only [rayStep,ite_eq_left hu,mul_one]
      · have hy := hp u z (by simp) (by omega)
        simp only [rayStep,hy,sub_self,zero_mul]
    simp only [rayIndex,hstep,ih ht]
    omega

/-- An arch attached across the boundary column has index one on every
primal boundary vertex between its endpoint heights. All other visited dual
face bases are in the positive half-plane. -/
theorem boundary_attached_arch_rayIndex (l u y : ℤ) (hgap : l+1 < u)
    (q : PD.squareLattice.Walk (-1,l) (-1,u))
    (hq : ∀ z ∈ q.support, 0 ≤ z.1 ∨ z = (-1,l) ∨ z = (-1,u))
    (hly : l < y) (hyu : y ≤ u) : rayIndex (0,y) q = 1 := by
  have hh : ∀ a b, s(a,b) ∈ q.edges → a.1 < (0 : ℤ) → a.2 = b.2 := by
    intro a b he ha
    have hA := hq a (q.fst_mem_support_of_mem_edges he)
    have hB := hq b (q.snd_mem_support_of_mem_edges he)
    have hadj := (squareLattice_adj_iff a b).mp (q.adj_of_mem_edges he)
    rcases hadj with ⟨_,hy⟩ | ⟨hx,hy⟩
    · exact hy
    · rcases hA with hA | rfl | rfl
      · omega
      all_goals
        rcases hB with hB | rfl | rfl <;> dsimp at * <;> omega
  rw [rayIndex_telescope_of_left_horizontal (0,y) q hh]
  simp only [ite_eq_left hly,ite_eq_right (not_lt.mpr hyu)]
  norm_num

end
end PottsContinuity.PlanarTopology
