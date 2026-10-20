module

public import PottsContinuity.Thm3.Prop4.CapsuleNearestNormal
public import PottsContinuity.Thm3.Prop4.CapsuleNormalSlopeAlgebra
public import PottsContinuity.Thm3.Prop4.TubeExitRegions

/-!
# An admissible supporting line at a maximal upper Euclidean excursion

The tangent direction is obtained from the genuine nearest-point normal.
The original square and chord slope force this direction to lie in the
full slope range of the corrected touch estimate, including endpoint caps.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- An upper capsule point in the original square has a supporting line of
slope at most one in absolute value. The line need not parallel the chord. -/
theorem exists_upper_capsule_supporting_line {n : ℕ} (hn : 1 ≤ n)
    (u v z : PD.FK.LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (hzB : z ∈ box n)
    (hzAbove : 0 < tubeLineOffset u v z) :
    ∃ s c : ℝ, |s| ≤ 1 ∧ (z.2 : ℝ) = s*z.1+c ∧
      (∀ w : ℂ, Metric.infDist w (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) ≤
        tubeDistance u v z → w.im ≤ s*w.re+c) ∧
      (∀ w : PD.FK.LatticeVertex, w ∈ box n → tubeLineOffset u v w ≤ 0 →
        (w.2 : ℝ) ≤ s*w.1+c) := by
  obtain ⟨t,b,ht,hu,hv⟩ := inductionTube_supporting_line hn u v huB hvB huX hvX
  obtain ⟨p,hp,hd,hnormal⟩ := exists_segment_nearest_normal
    (tubeLatticePoint u) (tubeLatticePoint v) (tubeLatticePoint z)
  let x := (tubeLatticePoint z-p).re
  let y := (tubeLatticePoint z-p).im
  let H := (z.2 : ℝ)-(t*z.1+b)
  have hdir : u.1 < v.1 := by rw [huX,hvX]; omega
  have hH : 0 < H := by
    by_contra h
    have hoff := (tubeLineOffset_nonpos_iff_deviation u v z t b hu hv hdir).mpr (le_of_not_gt h)
    omega
  have hpline := tube_segment_on_line u v t b hu hv hp
  have hrel : H = y-t*x := by
    dsimp [H,x,y,tubeLatticePoint]
    rw [hpline]
    ring
  have hzX : -(n : ℝ) ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ n := by
    have hz := hzB
    simp only [box,Finset.mem_product,Finset.mem_Icc] at hz
    exact ⟨by exact_mod_cast hz.1.1,by exact_mod_cast hz.1.2⟩
  let q : ℂ := ⟨(z.1 : ℝ),t*z.1+b⟩
  have hq := tube_supporting_line_mem_segment hn u v huX hvX t b (z.1 : ℝ) hu hv hzX
  have hqnormal := hnormal q hq
  have hdot : (star (tubeLatticePoint z-p)*(q-p)).re = x^2+y^2-y*H := by
    dsimp [x,y,H,q,tubeLatticePoint]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im]
    ring
  rw [hdot] at hqnormal
  have hineq : x^2+y^2 ≤ y*H := by linarith only [hqnormal]
  obtain ⟨hy,hxy⟩ := normal_vertical_dominates_of_upper_chord t x y H ht hH hrel hineq
  let s := -x/y
  let c := (z.2 : ℝ)-s*z.1
  have hs : |s| ≤ 1 := by
    dsimp [s]
    rw [abs_div,abs_neg,abs_of_pos hy]
    exact (div_le_iff₀ hy).mpr (by simpa only [one_mul] using hxy)
  have hcap : ∀ w : ℂ, Metric.infDist w (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) ≤
      tubeDistance u v z → w.im ≤ s*w.re+c := by
    intro w hw
    have hhalf := capsule_normal_half_plane_of_maximal_distance
      (tubeLatticePoint u) (tubeLatticePoint v) (tubeLatticePoint z) p w hnormal hd hw
    have hhalfDot : (star (tubeLatticePoint z-p)*(w-tubeLatticePoint z)).re =
        x*(w.re-z.1)+y*(w.im-z.2) := by
      dsimp [x,y,tubeLatticePoint]
      simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,
        Complex.sub_re,Complex.sub_im]
      ring
    rw [hhalfDot] at hhalf
    have hdiv : w.im-z.2 ≤ (-x*(w.re-z.1))/y :=
      (le_div_iff₀ hy).mpr (by linarith only [hhalf])
    have heq : (-x*(w.re-z.1))/y = s*w.re-s*z.1 := by dsimp [s]; ring
    rw [heq] at hdiv
    dsimp [c]
    linarith only [hdiv]
  refine ⟨s,c,hs,by dsimp [c]; ring,hcap,?_⟩
  intro w hwB hwBelow
  have hwX : -(n : ℝ) ≤ (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ n := by
    have hw := hwB
    simp only [box,Finset.mem_product,Finset.mem_Icc] at hw
    exact ⟨by exact_mod_cast hw.1.1,by exact_mod_cast hw.1.2⟩
  have hqmem := tube_supporting_line_mem_segment hn u v huX hvX t b (w.1 : ℝ) hu hv hwX
  have hqcap := hcap (⟨(w.1 : ℝ),t*w.1+b⟩ : ℂ) (by
    rw [Metric.infDist_zero_of_mem hqmem]
    exact tubeDistance_nonneg u v z)
  have hbelow := (tubeLineOffset_nonpos_iff_deviation u v w t b hu hv hdir).mp hwBelow
  change t*(w.1 : ℝ)+b ≤ s*w.1+c at hqcap
  linarith only [hbelow,hqcap]

end PottsContinuity.Thm3.Prop4
