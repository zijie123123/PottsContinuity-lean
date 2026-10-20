module

public import PottsContinuity.Thm3.Prop4.TubeWidth

/-!
# Admissible slopes for upper capsule normals

The variational inequality at the point directly below the excursion is a
scalar quadratic inequality. Together with the chord slope bound it forces
a positive vertical normal dominating its horizontal component.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The chord-height and normal inequalities force a positive, vertically
dominant normal, including the endpoint-projection cases. -/
theorem normal_vertical_dominates_of_upper_chord (t x y H : ℝ)
    (ht : |t| ≤ 1) (hH : 0 < H) (hrel : H = y-t*x)
    (hineq : x^2+y^2 ≤ y*H) : 0 < y ∧ |x| ≤ y := by
  have hy : 0 < y := by
    by_contra h
    have hy0 : y ≤ 0 := le_of_not_gt h
    have hm : y*H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy0 hH.le
    have hxSq : x^2 ≤ 0 := by linarith only [hineq,hm,sq_nonneg y]
    have hySq : y^2 ≤ 0 := by linarith only [hineq,hm,sq_nonneg x]
    have hxEq : x = 0 := sq_eq_zero_iff.mp (le_antisymm hxSq (sq_nonneg x))
    have hyEq : y = 0 := sq_eq_zero_iff.mp (le_antisymm hySq (sq_nonneg y))
    rw [hxEq,hyEq,mul_zero,sub_zero] at hrel
    exact (ne_of_gt hH) hrel
  refine ⟨hy,?_⟩
  rw [hrel] at hineq
  have hfactor : x*(x+t*y) ≤ 0 := by nlinarith only [hineq]
  have htBounds := abs_le.mp ht
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hh : 0 ≤ x+t*y := nonneg_of_mul_nonpos_right hfactor hx
    have hty := mul_le_mul_of_nonneg_right htBounds.2 hy.le
    rw [abs_of_neg hx]
    linarith only [hh,hty]
  · rw [hx,abs_zero]
    exact hy.le
  · have hh : x+t*y ≤ 0 := nonpos_of_mul_nonpos_right hfactor hx
    have hty := mul_le_mul_of_nonneg_right htBounds.1 hy.le
    rw [abs_of_pos hx]
    linarith only [hh,hty]

end PottsContinuity.Thm3.Prop4
