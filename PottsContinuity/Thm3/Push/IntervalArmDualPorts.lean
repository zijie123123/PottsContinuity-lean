module

public import PottsContinuity.PlanarTopology.ClampedDualConnector
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
open PottsContinuity.PlanarTopology
noncomputable section

/-- Exterior true-dual ports on the left side or strictly before the source
interval on the bottom. All coordinates are face-base coordinates. -/
def intervalArmLeftDualPorts (N : ℕ) (l : ℤ) : Finset (RectangleDualVertex (0,0) N N) := by
  classical
  letI : Fintype (RectangleDualVertex (0,0) N N) := Fintype.ofFinite _
  exact Finset.univ.filter fun z => z.val.1 = -1 ∨ z.val.2 = -1 ∧ z.val.1 < l

/-- Complementary exterior ports on the right side or at and after the right
endpoint of the source interval on the bottom. -/
def intervalArmRightDualPorts (N : ℕ) (r : ℤ) : Finset (RectangleDualVertex (0,0) N N) := by
  classical
  letI : Fintype (RectangleDualVertex (0,0) N N) := Fintype.ofFinite _
  exact Finset.univ.filter fun z => z.val.1 = (N : ℤ) ∨ z.val.2 = -1 ∧ r ≤ z.val.1

@[simp] theorem mem_intervalArmLeftDualPorts (N : ℕ) (l : ℤ)
    (z : RectangleDualVertex (0,0) N N) :
    z ∈ intervalArmLeftDualPorts N l ↔ z.val.1 = -1 ∨ z.val.2 = -1 ∧ z.val.1 < l := by
  classical
  simp only [intervalArmLeftDualPorts,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_intervalArmRightDualPorts (N : ℕ) (r : ℤ)
    (z : RectangleDualVertex (0,0) N N) :
    z ∈ intervalArmRightDualPorts N r ↔ z.val.1 = (N : ℤ) ∨ z.val.2 = -1 ∧ r ≤ z.val.1 := by
  classical
  simp only [intervalArmRightDualPorts,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Unit-mesh face centers before projection onto the closed source square. -/
theorem interval_arm_unit_face_center (z : LatticeVertex) :
    dualFaceCenter unitLatticeMesh z = (⟨(z.1 : ℝ)+1/2,(z.2 : ℝ)+1/2⟩ : ℂ) := by
  apply Complex.ext <;> norm_num [dualFaceCenter,latticeEmbed,unitLatticeMesh]

/-- Left seed ports project strictly to the left of every permitted starting
point, and remain on the left or bottom side. -/
theorem interval_arm_left_port_clamped (N : ℕ) (l : ℤ) (hl : 0 < l)
    (z : RectangleDualVertex (0,0) N N) (hz : z ∈ intervalArmLeftDualPorts N l) :
    let c := rectangleClamp (0,0) N N (dualFaceCenter unitLatticeMesh z.val)
    c.re < (l : ℝ) ∧ (c.re = 0 ∨ c.im = 0) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hcoord := (mem_intervalArmLeftDualPorts N l z).mp hz
  have hx : z.val.1+1 ≤ l := by rcases hcoord with h | ⟨_,h⟩ <;> omega
  have hxR : (z.val.1 : ℝ)+1 ≤ l := by exact_mod_cast hx
  dsimp only
  rw [interval_arm_unit_face_center]
  simp only [rectangleClamp, Int.cast_zero, zero_add]
  constructor
  · change max 0 (min (N : ℝ) ((z.val.1 : ℝ)+1/2)) < (l : ℝ)
    exact max_lt hlR ((min_le_right _ _).trans_lt (by linarith))
  · rcases hcoord with hx | ⟨hy,_⟩
    · left
      have hxR : (z.val.1 : ℝ) = -1 := by exact_mod_cast hx
      change max 0 (min (N : ℝ) ((z.val.1 : ℝ)+1/2)) = 0
      apply max_eq_left
      exact (min_le_right _ _).trans (by linarith)
    · right
      have hyR : (z.val.2 : ℝ) = -1 := by exact_mod_cast hy
      change max 0 (min (N : ℝ) ((z.val.2 : ℝ)+1/2)) = 0
      apply max_eq_left
      exact (min_le_right _ _).trans (by linarith)

/-- Right seed ports project strictly to the right of every permitted starting
point, and remain on the right or bottom side. -/
theorem interval_arm_right_port_clamped (N : ℕ) (r : ℤ) (hr : r < (N : ℤ))
    (z : RectangleDualVertex (0,0) N N) (hz : z ∈ intervalArmRightDualPorts N r) :
    let c := rectangleClamp (0,0) N N (dualFaceCenter unitLatticeMesh z.val)
    (r : ℝ) < c.re ∧ (c.re = (N : ℝ) ∨ c.im = 0) := by
  have hrR : (r : ℝ) < N := by exact_mod_cast hr
  have hcoord := (mem_intervalArmRightDualPorts N r z).mp hz
  have hx : r ≤ z.val.1 := by rcases hcoord with h | ⟨_,h⟩ <;> omega
  have hxR : (r : ℝ) ≤ z.val.1 := by exact_mod_cast hx
  dsimp only
  rw [interval_arm_unit_face_center]
  simp only [rectangleClamp, Int.cast_zero, zero_add]
  constructor
  · change (r : ℝ) < max 0 (min (N : ℝ) ((z.val.1 : ℝ)+1/2))
    exact (lt_min (by linarith) (by linarith)).trans_le (le_max_right _ _)
  · rcases hcoord with hx | ⟨hy,_⟩
    · left
      have hxR : (z.val.1 : ℝ) = N := by exact_mod_cast hx
      change max 0 (min (N : ℝ) ((z.val.1 : ℝ)+1/2)) = N
      rw [min_eq_left (by linarith),max_eq_right (Nat.cast_nonneg N)]
    · right
      have hyR : (z.val.2 : ℝ) = -1 := by exact_mod_cast hy
      change max 0 (min (N : ℝ) ((z.val.2 : ℝ)+1/2)) = 0
      apply max_eq_left
      exact (min_le_right _ _).trans (by linarith)

end
end PottsContinuity.Push
