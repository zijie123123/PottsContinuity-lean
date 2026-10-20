module

public import PottsContinuity.Thm3.Prop4.TubeColumnConvex
public import PottsContinuity.Thm3.Prop4.TubeCutNonempty

/-! # Vertical interpolation towards the supporting segment stays in the tube -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Vertical interpolation is a literal real segment, including equal heights. -/
theorem complex_vertical_mem_segment (x a y b : ℝ) (hay : a ≤ y) (hyb : y ≤ b) :
    (⟨x,y⟩ : ℂ) ∈ segment ℝ (⟨x,a⟩ : ℂ) (⟨x,b⟩ : ℂ) := by
  by_cases hab : a = b
  · have hya : y = a := le_antisymm (hab ▸ hyb) hay
    rw [hya]
    exact left_mem_segment ℝ _ _
  have hpos : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne (hay.trans hyb) hab)
  refine ⟨(b-y)/(b-a),(y-a)/(b-a),div_nonneg (sub_nonneg.mpr hyb) hpos.le,
    div_nonneg (sub_nonneg.mpr hay) hpos.le,?_,?_⟩
  · field_simp
    ring
  · apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,
      Complex.smul_im,smul_eq_mul] <;> field_simp <;> ring

/-- On the upper side of the supporting segment, moving vertically down
from a tube vertex towards the segment retains the exact Euclidean tube. -/
theorem radiusTube_vertical_down_towards_line {n : ℕ} (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 < R) (u v : ℤ × ℤ)
    (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.2 : ℝ) = t*u.1+b) (hvt : (v.2 : ℝ) = t*v.1+b)
    (k y z : ℤ) (hzB : (k,z) ∈ box n) (hyT : (k,y) ∈ radiusTube n R u v)
    (hzy : z ≤ y) (hline : t*k+b ≤ (z : ℝ)) : (k,z) ∈ radiusTube n R u v := by
  have hx : -(n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ n := by
    have hh := (Finset.mem_product.mp hzB).1
    exact_mod_cast Finset.mem_Icc.mp hh
  have hc := tube_supporting_line_mem_segment hn u v hu hv t b (k : ℝ) hut hvt hx
  have hct : Metric.infDist (⟨(k : ℝ),t*k+b⟩ : ℂ)
      (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) < R := by
    rw [Metric.infDist_zero_of_mem hc]
    exact hR
  have hyt := ((mem_radiusTube n R u v (k,y)).mp hyT).2
  apply (mem_radiusTube n R u v (k,z)).mpr
  refine ⟨hzB,?_⟩
  exact (convex_euclidean_tube u v R).segment_subset hct hyt
    (complex_vertical_mem_segment (k : ℝ) (t*k+b) z y hline (by exact_mod_cast hzy))

/-- The corresponding move upwards towards the supporting segment also
retains the literal Euclidean tube. -/
theorem radiusTube_vertical_up_towards_line {n : ℕ} (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 < R) (u v : ℤ × ℤ)
    (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.2 : ℝ) = t*u.1+b) (hvt : (v.2 : ℝ) = t*v.1+b)
    (k y z : ℤ) (hzB : (k,z) ∈ box n) (hyT : (k,y) ∈ radiusTube n R u v)
    (hyz : y ≤ z) (hline : (z : ℝ) ≤ t*k+b) : (k,z) ∈ radiusTube n R u v := by
  have hx : -(n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ n := by
    have hh := (Finset.mem_product.mp hzB).1
    exact_mod_cast Finset.mem_Icc.mp hh
  have hc := tube_supporting_line_mem_segment hn u v hu hv t b (k : ℝ) hut hvt hx
  have hct : Metric.infDist (⟨(k : ℝ),t*k+b⟩ : ℂ)
      (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) < R := by
    rw [Metric.infDist_zero_of_mem hc]
    exact hR
  have hyt := ((mem_radiusTube n R u v (k,y)).mp hyT).2
  apply (mem_radiusTube n R u v (k,z)).mpr
  refine ⟨hzB,?_⟩
  exact (convex_euclidean_tube u v R).segment_subset hyt hct
    (complex_vertical_mem_segment (k : ℝ) y z (t*k+b) (by exact_mod_cast hyz) hline)

end
end PottsContinuity.Thm3.Prop4
