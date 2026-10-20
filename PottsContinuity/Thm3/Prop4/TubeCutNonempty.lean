module

public import PottsContinuity.Thm3.Prop4.TubeColumnConvex
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import PottsContinuity.Thm3.Prop4.RadiusTubeSurgery
public import PottsContinuity.PD.FK.FrozenLimitBridge

/-!
# Nonempty central cuts for opposite-face Euclidean tubes

A rounded height at the midpoint belongs to both central columns when the
radius is at least two. The supporting line is used only to exhibit points
on the original segment; the tube retains its Euclidean definition.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Real points on the supporting line between the two vertical faces lie on the segment. -/
theorem tube_supporting_line_mem_segment {n : ℕ} (hn : 1 ≤ n)
    (u v : ℤ × ℤ) (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b x : ℝ) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (hx : -(n : ℝ) ≤ x ∧ x ≤ n) :
    (⟨x,t*x+b⟩ : ℂ) ∈ segment ℝ (tubeLatticePoint u) (tubeLatticePoint v) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨((n : ℝ)-x)/(2*n),(x+(n : ℝ))/(2*n),
    div_nonneg (sub_nonneg.mpr hx.2) (by positivity),
    div_nonneg (by linarith only [hx.1]) (by positivity),?_,?_⟩
  · field_simp
    ring
  · apply Complex.ext
    · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
      change (((n : ℝ)-x)/(2*n))*(u.1 : ℝ) +
        ((x+(n : ℝ))/(2*n))*(v.1 : ℝ) = x
      rw [ha,hb]
      push_cast
      field_simp
      ring
    · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
      change (((n : ℝ)-x)/(2*n))*(u.2 : ℝ) +
        ((x+(n : ℝ))/(2*n))*(v.2 : ℝ) = t*x+b
      rw [hu,hv,ha,hb]
      push_cast
      field_simp
      ring

/-- The vertical distance to a supporting-line point bounds the actual segment distance. -/
theorem tubeDistance_le_supporting_vertical {n : ℕ} (hn : 1 ≤ n)
    (u v : ℤ × ℤ) (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (k y : ℤ)
    (hk : -(n : ℤ) ≤ k ∧ k ≤ n) :
    tubeDistance u v (k,y) ≤ |(y : ℝ)-(t*k+b)| := by
  have hkR : -(n : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ n := by exact_mod_cast hk
  have hm := tube_supporting_line_mem_segment hn u v ha hb t b (k : ℝ) hu hv hkR
  refine (Metric.infDist_le_dist_of_mem hm).trans ?_
  rw [dist_eq_norm]
  have h := Complex.norm_le_abs_re_add_abs_im
    (tubeLatticePoint (k,y) - (⟨(k : ℝ),t*k+b⟩ : ℂ))
  simpa [tubeLatticePoint] using h

/-- The central cut is nonempty for every radius at least two. -/
theorem radiusTubeCutRows_zero_nonempty {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 2 ≤ r) (u v : ℤ × ℤ) (hu : u ∈ box n) (hv : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ)) :
    (radiusTubeCutRows n r u v 0).Nonempty := by
  classical
  obtain ⟨t,b,ht,huL,hvL⟩ := inductionTube_supporting_line hn u v hu hv ha hb
  have huY : -(n : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ n := by
    have h : -(n : ℤ) ≤ u.2 ∧ u.2 ≤ n :=
      (Finset.mem_product.mp hu).2 |> Finset.mem_Icc.mp
    exact_mod_cast h
  have hvY : -(n : ℝ) ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) ≤ n := by
    have h : -(n : ℤ) ≤ v.2 ∧ v.2 ≤ n :=
      (Finset.mem_product.mp hv).2 |> Finset.mem_Icc.mp
    exact_mod_cast h
  rw [ha] at huL
  rw [hb] at hvL
  push_cast at huL hvL
  have hbLo : -(n : ℝ) ≤ b := by linarith only [huY.1,hvY.1,huL,hvL]
  have hbHi : b ≤ (n : ℝ) := by linarith only [huY.2,hvY.2,huL,hvL]
  let y : ℤ := ⌈b⌉
  have hyLo : b ≤ (y : ℝ) := Int.le_ceil b
  have hyHi : (y : ℝ) < b+1 := Int.ceil_lt_add_one b
  have hyBox : -(n : ℤ) ≤ y ∧ y ≤ n := by
    constructor
    · exact_mod_cast hbLo.trans hyLo
    · exact Int.ceil_le.mpr hbHi
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have ht' := abs_le.mp ht
  have hzero : |(y : ℝ)-(t*(0 : ℤ)+b)| < 2 := by
    rw [abs_lt]
    constructor <;> push_cast <;> nlinarith only [hyLo,hyHi]
  have hone : |(y : ℝ)-(t*(1 : ℤ)+b)| < 2 := by
    rw [abs_lt]
    constructor <;> push_cast <;> nlinarith only [hyLo,hyHi,ht'.1,ht'.2]
  refine ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hyBox,?_,?_⟩⟩
  · apply (mem_radiusTube n r u v (0,y)).mpr
    refine ⟨?_,lt_of_lt_of_le ?_ hr⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega),Finset.mem_Icc.mpr hyBox⟩
    · exact (tubeDistance_le_supporting_vertical hn u v ha hb t b
        (by simpa [ha] using huL) (by simpa [hb] using hvL) 0 y (by omega)).trans_lt hzero
  · apply (mem_radiusTube n r u v (1,y)).mpr
    refine ⟨?_,lt_of_lt_of_le ?_ hr⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega),Finset.mem_Icc.mpr hyBox⟩
    · exact (tubeDistance_le_supporting_vertical hn u v ha hb t b
        (by simpa [ha] using huL) (by simpa [hb] using hvL) 1 y (by omega)).trans_lt hone

end PottsContinuity.Thm3.Prop4
