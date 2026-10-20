module

public import PottsContinuity.Thm3.Prop4.CorridorRows
public import PottsContinuity.Thm3.Prop4.TubeCutNonempty

/-!
# Euclidean tube containment from the actual corridor centers

All distances refer to the original segment in the complex Euclidean plane.
Rounding and inward clamping are included in the margin 4s+1. No lattice
rotation or assumption about an integral midpoint is used.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every supporting-line point above a box abscissa has height inside the box. -/
theorem tube_supporting_line_height_bounds {n : ℕ}
    (u v : ℤ × ℤ) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (x : ℤ)
    (hx : -(n : ℤ) ≤ x ∧ x ≤ n) :
    -(n : ℝ) ≤ t*(x : ℝ)+b ∧ t*(x : ℝ)+b ≤ n := by
  have huY : -(n : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ n := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_product.mp huB).2)
    exact_mod_cast hh
  have hvY : -(n : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ n := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_product.mp hvB).2)
    exact_mod_cast hh
  have hxR : -(n : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ n := by exact_mod_cast hx
  rw [ha] at hu
  rw [hb] at hv
  push_cast at hu hv
  rcases le_total 0 t with ht | ht
  · have h₁ := mul_le_mul_of_nonneg_left hxR.1 ht
    have h₂ := mul_le_mul_of_nonneg_left hxR.2 ht
    constructor <;> linarith only [h₁,h₂,hu,hv,huY.1,huY.2,hvY.1,hvY.2]
  · have h₁ := mul_le_mul_of_nonpos_left hxR.1 ht
    have h₂ := mul_le_mul_of_nonpos_left hxR.2 ht
    constructor <;> linarith only [h₁,h₂,hu,hv,huY.1,huY.2,hvY.1,hvY.2]

/-- The full neighborhood needed by a connector lies in the literal Euclidean tube. -/
theorem corridor_point_mem_radiusTube {n : ℕ} (hn : 1 ≤ n)
    (s : ℕ) (hs : s ≤ n) (u v : ℤ × ℤ) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (x : ℤ) (hx : -(n : ℤ) ≤ x ∧ x ≤ n)
    (z : ℤ × ℤ) (hzB : z ∈ box n)
    (hzx : |z.1-x| ≤ (s : ℤ))
    (hzy : |z.2-corridorRow n s hs t b x| ≤ 2*(s : ℤ))
    (R : ℝ) (hR : 4*(s : ℝ)+1 ≤ R) : z ∈ radiusTube n R u v := by
  have hc := corridorRow_line_deviation n s hs t b x
    (tube_supporting_line_height_bounds u v huB hvB ha hb t b hu hv x hx)
  have hzxR : |(z.1 : ℝ)-(x : ℝ)| ≤ (s : ℝ) := by exact_mod_cast hzx
  have hzyR : |(z.2 : ℝ)-(corridorRow n s hs t b x : ℝ)| ≤ 2*(s : ℝ) := by exact_mod_cast hzy
  have hprod : |t*((x : ℝ)-(z.1 : ℝ))| ≤ (s : ℝ) := by
    rw [abs_mul,abs_sub_comm (x : ℝ)]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa only [one_mul] using hzxR)
  have htriangle : |(z.2 : ℝ)-(t*(z.1 : ℝ)+b)| ≤
      |(z.2 : ℝ)-(corridorRow n s hs t b x : ℝ)| +
      |(corridorRow n s hs t b x : ℝ)-(t*(x : ℝ)+b)| + |t*((x : ℝ)-(z.1 : ℝ))| := by
    have he : (z.2 : ℝ)-(t*(z.1 : ℝ)+b) =
      ((z.2 : ℝ)-(corridorRow n s hs t b x : ℝ)) +
      ((corridorRow n s hs t b x : ℝ)-(t*(x : ℝ)+b)) + t*((x : ℝ)-(z.1 : ℝ)) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hd : |(z.2 : ℝ)-(t*(z.1 : ℝ)+b)| < R := by
    linarith only [htriangle,hzyR,hc,hprod,hR]
  apply (mem_radiusTube n R u v z).mpr
  refine ⟨hzB,?_⟩
  have hzxB := Finset.mem_Icc.mp (Finset.mem_product.mp hzB).1
  exact (tubeDistance_le_supporting_vertical hn u v ha hb t b hu hv z.1 z.2 hzxB).trans_lt hd

end PottsContinuity.Thm3.Prop4
