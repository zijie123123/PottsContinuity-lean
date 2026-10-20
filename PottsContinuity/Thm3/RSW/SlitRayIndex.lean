module

public import PottsContinuity.PlanarTopology.InterlacedPaths
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarTopology
noncomputable section

/-- Close the actual bottom-to-tip walk outside the box. The right neighbor
of a missing higher slit vertex and the earlier bottom start have different indices. -/
theorem exists_slit_tip_loop_with_ray_indices
    (a b B x y H z : ℤ) (hab : a < b) (hyz : y < z) (hzH : z ≤ H)
    (q : squareLattice.Walk (b,0) (x,y))
    (hq : ∀ w ∈ q.support, x ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ H)
    (hmark : (x,z) ∉ q.support) :
    ∃ C : squareLattice.Walk (b,0) (b,0),
      (∀ w ∈ C.support,
        w ∈ q.support ∨ (w.1 = x ∧ y ≤ w.2) ∨ H < w.2 ∨ B < w.1 ∨ w.2 < 0) ∧
      rayIndex (a,0) C = 0 ∧ rayIndex (x+1,z) C = -1 := by
  have hb := hq (b,0) q.start_mem_support
  have ht := hq (x,y) q.end_mem_support
  have hy : 0 ≤ y := ht.2.2.1
  have hH : 0 ≤ H := hb.2.2.2
  obtain ⟨R,hR⟩ := vertical_walk_between x y (H+1)
  obtain ⟨T,hT⟩ := horizontal_walk_between x (B+1) (H+1)
  obtain ⟨D,hD⟩ := vertical_walk_between (B+1) (H+1) (-1)
  obtain ⟨L,hL⟩ := horizontal_walk_between (B+1) b (-1)
  have hup : squareLattice.Adj (b,-1) (b,0) := by
    rw [squareLattice_adj_iff]; dsimp; omega
  let C := q.append (R.append (T.append (D.append (L.append hup.toWalk))))
  have hqs : rayIndex (a,0) q = 0 := by
    apply rayIndex_zero_of_level (a,0) q 0
    intro w hw
    exact ite_eq_right (by have := (hq w hw).2.2.1; dsimp; omega)
  have hqz : rayIndex (x+1,z) q = 0 := by
    have hedge : s((x,z-1),(x,z)) ∉ q.edges := by
      intro he
      exact hmark (q.snd_mem_support_of_mem_edges he)
    rw [← rayIndex_horizontal_invariant x z q hedge]
    rw [rayIndex_left_telescope (x,z) q (fun w hw => (hq w hw).1)]
    simp only [ite_eq_left (by omega : (0:ℤ) < z),ite_eq_left hyz,sub_self]
  have hRs : rayIndex (a,0) R = 0 := by
    apply rayIndex_zero_of_level (a,0) R 0
    intro w hw
    have hh := hR w hw
    rw [min_eq_left (by omega : y ≤ H+1)] at hh
    exact ite_eq_right (by dsimp; omega)
  have hRz : rayIndex (x+1,z) R = 0 := by
    apply rayIndex_zero_of_right
    intro w hw
    have hh := (hR w hw).1
    dsimp
    omega
  have hTs : rayIndex (a,0) T = 0 := by
    apply rayIndex_zero_of_level (a,0) T 0
    intro w hw
    have hh := (hT w hw).2.2
    exact ite_eq_right (by dsimp; omega)
  have hTz : rayIndex (x+1,z) T = 0 := by
    apply rayIndex_zero_of_level (x+1,z) T 0
    intro w hw
    have hh := (hT w hw).2.2
    exact ite_eq_right (by dsimp; omega)
  have hDs : rayIndex (a,0) D = -1 := by
    rw [rayIndex_left_telescope (a,0) D (by
      intro w hw; have hh := (hD w hw).1; dsimp; omega)]
    norm_num [show ¬ H+1 < 0 by omega]
  have hDz : rayIndex (x+1,z) D = -1 := by
    rw [rayIndex_left_telescope (x+1,z) D (by
      intro w hw; have hh := (hD w hw).1; dsimp; omega)]
    simp only [ite_eq_right (by omega : ¬ H+1 < z),
      ite_eq_left (by omega : (-1:ℤ) < z)]
    norm_num
  have hLs : rayIndex (a,0) L = 0 := by
    apply rayIndex_zero_of_level (a,0) L 1
    intro w hw
    rw [(hL w hw).2.2]
    norm_num
  have hLz : rayIndex (x+1,z) L = 0 := by
    apply rayIndex_zero_of_level (x+1,z) L 1
    intro w hw
    rw [(hL w hw).2.2]
    exact ite_eq_left (by dsimp; omega)
  have hUs : rayIndex (a,0) hup.toWalk = 1 := by
    simp [rayIndex,rayStep,show a ≤ b by omega]
  have hUz : rayIndex (x+1,z) hup.toWalk = 0 := by
    simp [rayIndex,rayStep,show (-1:ℤ) < z by omega,show (0:ℤ) < z by omega]
  refine ⟨C,?_,?_,?_⟩
  · intro w hw
    change w ∈ (q.append (R.append (T.append (D.append (L.append hup.toWalk))))).support at hw
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw | hw | hw | hw | hw
    · exact Or.inl hw
    · have hh := hR w hw
      rw [min_eq_left (by omega : y ≤ H+1)] at hh
      exact Or.inr (Or.inl ⟨hh.1,hh.2.1⟩)
    · have hh := (hT w hw).2.2
      exact Or.inr (Or.inr (Or.inl (by omega)))
    · have hh := (hD w hw).1
      exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · have hh := (hL w hw).2.2
      exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    · have he : w = (b,-1) ∨ w = (b,0) := by simpa using hw
      rcases he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by norm_num))))
      · exact Or.inl q.start_mem_support
  · simp only [C,rayIndex_append,hqs,hRs,hTs,hDs,hLs,hUs]
    norm_num
  · simp only [C,rayIndex_append,hqz,hRz,hTz,hDz,hLz,hUz]
    norm_num

end
end PottsContinuity.RSW
