-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/SquareBoundaryWinding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.WindingCircle

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval

noncomputable section

def clockwiseSquareTopLeft : ℂ := (-1 : ℂ) + Complex.I
def clockwiseSquareTopRight : ℂ := (1 : ℂ) + Complex.I
def clockwiseSquareBottomRight : ℂ := (1 : ℂ) - Complex.I
def clockwiseSquareBottomLeft : ℂ := (-1 : ℂ) - Complex.I

def clockwiseSquareBoundary : Path clockwiseSquareTopLeft clockwiseSquareTopLeft :=
  ((Path.segment clockwiseSquareTopLeft clockwiseSquareTopRight).trans
    (Path.segment clockwiseSquareTopRight clockwiseSquareBottomRight)).trans
  ((Path.segment clockwiseSquareBottomRight clockwiseSquareBottomLeft).trans
    (Path.segment clockwiseSquareBottomLeft clockwiseSquareTopLeft))

def clockwiseCircleAtSquarePhase : Path
    ((Circle.exp (3 * Real.pi / 4) : Circle) : ℂ)
    ((Circle.exp (3 * Real.pi / 4) : Circle) : ℂ) where
  toFun t := (Circle.exp (3 * Real.pi / 4 - 2 * Real.pi * t) : ℂ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    have hperiod (x : ℝ) : Circle.exp (x - 2 * Real.pi) = Circle.exp x := by
      rw [Circle.exp_sub]
      have htwo : Circle.exp (2 * Real.pi) = 1 := by
        apply Subtype.ext
        rw [Circle.coe_exp]
        convert Complex.exp_two_pi_mul_I using 1 <;> push_cast <;> ring
      rw [htwo, div_one]
    change (Circle.exp (3 * Real.pi / 4 - 2 * Real.pi * (1 : ℝ)) : ℂ) = _
    rw [show 3 * Real.pi / 4 - 2 * Real.pi * (1 : ℝ) =
      3 * Real.pi / 4 - 2 * Real.pi by ring, hperiod]

@[simp] theorem clockwiseCircleAtSquarePhase_apply (t : I) :
    clockwiseCircleAtSquarePhase t =
      (Circle.exp (3 * Real.pi / 4 - 2 * Real.pi * t) : ℂ) := rfl

def squareCircleHomotopy : C(I × I, ℂ) where
  toFun u := (1 - (u.1 : ℝ)) • clockwiseSquareBoundary u.2 +
      (u.1 : ℝ) • clockwiseCircleAtSquarePhase u.2
  continuous_toFun := by fun_prop

theorem clockwiseSquareBoundary_avoids_zero :
    (0 : ℂ) ∉ Set.range clockwiseSquareBoundary := by
  have ht : (0 : ℂ) ∉ Set.range
      (Path.segment clockwiseSquareTopLeft clockwiseSquareTopRight) := by
    rintro ⟨t, ht⟩
    have him := congrArg Complex.im ht
    have hval : (Path.segment clockwiseSquareTopLeft clockwiseSquareTopRight t).im = 1 := by
      change (AffineMap.lineMap clockwiseSquareTopLeft clockwiseSquareTopRight (t : ℝ)).im = 1
      rw [AffineMap.lineMap_apply_module]
      simp only [Complex.add_im, Complex.real_smul,
        ]
      norm_num [clockwiseSquareTopLeft, clockwiseSquareTopRight]
    rw [ht] at hval
    norm_num at hval
  have hr : (0 : ℂ) ∉ Set.range
      (Path.segment clockwiseSquareTopRight clockwiseSquareBottomRight) := by
    rintro ⟨t, ht⟩
    have hre := congrArg Complex.re ht
    have hval : (Path.segment clockwiseSquareTopRight clockwiseSquareBottomRight t).re = 1 := by
      change (AffineMap.lineMap clockwiseSquareTopRight clockwiseSquareBottomRight (t : ℝ)).re = 1
      rw [AffineMap.lineMap_apply_module]
      simp only [Complex.add_re, Complex.real_smul,
        ]
      norm_num [clockwiseSquareTopRight, clockwiseSquareBottomRight]
    rw [ht] at hval
    norm_num at hval
  have hb : (0 : ℂ) ∉ Set.range
      (Path.segment clockwiseSquareBottomRight clockwiseSquareBottomLeft) := by
    rintro ⟨t, ht⟩
    have him := congrArg Complex.im ht
    have hval : (Path.segment clockwiseSquareBottomRight clockwiseSquareBottomLeft t).im = -1 := by
      change (AffineMap.lineMap clockwiseSquareBottomRight clockwiseSquareBottomLeft (t : ℝ)).im = -1
      rw [AffineMap.lineMap_apply_module]
      simp only [Complex.add_im, Complex.real_smul,
        ]
      norm_num [clockwiseSquareBottomRight, clockwiseSquareBottomLeft]
      ring
    rw [ht] at hval
    norm_num at hval
  have hl : (0 : ℂ) ∉ Set.range
      (Path.segment clockwiseSquareBottomLeft clockwiseSquareTopLeft) := by
    rintro ⟨t, ht⟩
    have hre := congrArg Complex.re ht
    have hval : (Path.segment clockwiseSquareBottomLeft clockwiseSquareTopLeft t).re = -1 := by
      change (AffineMap.lineMap clockwiseSquareBottomLeft clockwiseSquareTopLeft (t : ℝ)).re = -1
      rw [AffineMap.lineMap_apply_module]
      simp only [Complex.add_re, Complex.real_smul,
        ]
      norm_num [clockwiseSquareBottomLeft, clockwiseSquareTopLeft]
      ring
    rw [ht] at hval
    norm_num at hval
  intro hz
  change (0 : ℂ) ∈ Set.range
    (((Path.segment clockwiseSquareTopLeft clockwiseSquareTopRight).trans
      (Path.segment clockwiseSquareTopRight clockwiseSquareBottomRight)).trans
    ((Path.segment clockwiseSquareBottomRight clockwiseSquareBottomLeft).trans
      (Path.segment clockwiseSquareBottomLeft clockwiseSquareTopLeft))) at hz
  rw [Path.trans_range] at hz
  rcases hz with hzTop | hzBottom
  · rw [Path.trans_range] at hzTop
    rcases hzTop with hz | hz
    · exact ht hz
    · exact hr hz
  · rw [Path.trans_range] at hzBottom
    rcases hzBottom with hz | hz
    · exact hb hz
    · exact hl hz

theorem clockwiseCircleAtSquarePhase_avoids_zero :
    (0 : ℂ) ∉ Set.range clockwiseCircleAtSquarePhase := by
  rintro ⟨t, ht⟩
  exact (Circle.exp (3 * Real.pi / 4 - 2 * Real.pi * t)).coe_ne_zero ht

theorem clockwiseCircleAtSquarePhase_top_im_pos (t : I)
    (ht : (t : ℝ) ≤ 1 / 4) : 0 < (clockwiseCircleAtSquarePhase t).im := by
  rw [clockwiseCircleAtSquarePhase_apply, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    add_zero, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    ]
  have hsin := Real.sin_pos_of_pos_of_lt_pi (x := 3 * Real.pi / 4 - 2 * Real.pi * (t : ℝ))
    (by have hpi : 0 < Real.pi := Real.pi_pos; nlinarith [t.2.1])
    (by have hpi : 0 < Real.pi := Real.pi_pos; have hp := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) t.2.1; nlinarith)
  simpa using hsin

theorem clockwiseSquareBoundary_top_im (t : I)
    (ht : (t : ℝ) ≤ 1 / 4) : (clockwiseSquareBoundary t).im = 1 := by
  rw [clockwiseSquareBoundary, Path.trans_apply]
  have hfirst : (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_left hfirst, Path.trans_apply]
  have hsecond : 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_left hsecond]
  change (AffineMap.lineMap clockwiseSquareTopLeft clockwiseSquareTopRight
    (2 * (2 * (t : ℝ)))).im = 1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_im, Complex.real_smul,
    ]
  norm_num [clockwiseSquareTopLeft, clockwiseSquareTopRight]

theorem clockwiseCircleAtSquarePhase_right_re_pos (t : I)
    (h₁ : 1 / 4 < (t : ℝ)) (h₂ : (t : ℝ) ≤ 1 / 2) :
    0 < (clockwiseCircleAtSquarePhase t).re := by
  rw [clockwiseCircleAtSquarePhase_apply, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    mul_one]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> have hpi : 0 < Real.pi := Real.pi_pos <;>
    have hleft := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (sub_nonneg.mpr h₁.le) <;>
    have hright := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (sub_nonneg.mpr h₂) <;>
    nlinarith

theorem clockwiseCircleAtSquarePhase_bottom_im_neg (t : I)
    (h₁ : 1 / 2 < (t : ℝ)) (h₂ : (t : ℝ) ≤ 3 / 4) :
    (clockwiseCircleAtSquarePhase t).im < 0 := by
  rw [clockwiseCircleAtSquarePhase_apply, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, add_zero,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero]
  have hangle : 3 * Real.pi / 4 - 2 * Real.pi * (t : ℝ) =
      -(2 * Real.pi * (t : ℝ) - 3 * Real.pi / 4) := by ring
  rw [hangle, Real.sin_neg]
  have hsin : 0 < Real.sin (2 * Real.pi * (t : ℝ) - 3 * Real.pi / 4) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hp := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (sub_nonneg.mpr h₁.le)
      nlinarith
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hp := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (sub_nonneg.mpr h₂)
      nlinarith
  linarith

theorem clockwiseCircleAtSquarePhase_left_re_neg (t : I)
    (h₁ : 3 / 4 < (t : ℝ)) :
    (clockwiseCircleAtSquarePhase t).re < 0 := by
  rw [clockwiseCircleAtSquarePhase_apply, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
  have hangle : 3 * Real.pi / 4 - 2 * Real.pi * (t : ℝ) =
      -(2 * Real.pi * (t : ℝ) - 3 * Real.pi / 4) := by ring
  rw [hangle, Real.cos_neg]
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · have hpi : 0 < Real.pi := Real.pi_pos
    have hp := mul_pos (by positivity : 0 < 2 * Real.pi) (sub_pos.mpr h₁)
    nlinarith
  · have hpi : 0 < Real.pi := Real.pi_pos
    have hp := mul_le_mul_of_nonneg_left t.2.2 (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith

theorem clockwiseSquareBoundary_right_re (t : I)
    (h₁ : 1 / 4 < (t : ℝ)) (h₂ : (t : ℝ) ≤ 1 / 2) :
    (clockwiseSquareBoundary t).re = 1 := by
  rw [clockwiseSquareBoundary, Path.trans_apply]
  have hfirst : (t : ℝ) ≤ 1 / 2 := h₂
  rw [dite_eq_left hfirst, Path.trans_apply]
  have hsecond : ¬ 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_right hsecond]
  change (AffineMap.lineMap clockwiseSquareTopRight clockwiseSquareBottomRight
    (2 * (2 * (t : ℝ)) - 1)).re = 1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.real_smul,
    ]
  norm_num [clockwiseSquareTopRight, clockwiseSquareBottomRight]

theorem clockwiseSquareBoundary_bottom_im (t : I)
    (h₁ : 1 / 2 < (t : ℝ)) (h₂ : (t : ℝ) ≤ 3 / 4) :
    (clockwiseSquareBoundary t).im = -1 := by
  rw [clockwiseSquareBoundary, Path.trans_apply]
  have hfirst : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_right hfirst, Path.trans_apply]
  have hsecond : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [dite_eq_left hsecond]
  change (AffineMap.lineMap clockwiseSquareBottomRight clockwiseSquareBottomLeft
    (2 * (2 * (t : ℝ) - 1))).im = -1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_im, Complex.real_smul,
    ]
  norm_num [clockwiseSquareBottomRight, clockwiseSquareBottomLeft]
  ring

theorem clockwiseSquareBoundary_left_re (t : I)
    (h₁ : 3 / 4 < (t : ℝ)) :
    (clockwiseSquareBoundary t).re = -1 := by
  rw [clockwiseSquareBoundary, Path.trans_apply]
  have hfirst : ¬ (t : ℝ) ≤ 1 / 2 := by linarith [h₁]
  rw [dite_eq_right hfirst, Path.trans_apply]
  have hsecond : ¬ 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [dite_eq_right hsecond]
  change (AffineMap.lineMap clockwiseSquareBottomLeft clockwiseSquareTopLeft
    (2 * (2 * (t : ℝ) - 1) - 1)).re = -1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.real_smul,
    ]
  norm_num [clockwiseSquareBottomLeft, clockwiseSquareTopLeft]


lemma convexCombination_pos {x y r : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 < (1 - r) * x + r * y := by
  by_cases hr : r = 1
  · simp [hr, hy]
  · have hcoef : 0 < 1 - r := by
      have hrlt : r < 1 := by
        by_contra hnot
        have hge : 1 ≤ r := le_of_not_gt hnot
        exact hr (le_antisymm hr1 hge)
      linarith
    have hleft : 0 < (1 - r) * x := mul_pos hcoef hx
    have hright : 0 ≤ r * y := mul_nonneg hr0 (le_of_lt hy)
    linarith

def squareCircleHomotopyLoop (u : I × I) : ℂ := squareCircleHomotopy u

theorem squareCircleHomotopy_avoids_zero (u : I × I) :
    squareCircleHomotopyLoop u ≠ 0 := by
  intro hz0
  let s : ℝ := u.1
  let t : I := u.2
  have hs0 : 0 ≤ s := u.1.2.1
  have hs1 : s ≤ 1 := u.1.2.2
  have him : (squareCircleHomotopyLoop u).im =
      (1 - s) * (clockwiseSquareBoundary t).im +
        s * (clockwiseCircleAtSquarePhase t).im := by
    simp [squareCircleHomotopyLoop, squareCircleHomotopy, s, t,
      Complex.add_im, Complex.real_smul]
  by_cases htop : (t : ℝ) ≤ 1 / 4
  · have hsq : 0 < (clockwiseSquareBoundary t).im := by
      rw [clockwiseSquareBoundary_top_im t htop]; norm_num
    have hci := clockwiseCircleAtSquarePhase_top_im_pos t htop
    have hmix := convexCombination_pos hsq hci hs0 hs1
    have hz := congrArg Complex.im (hz0)
    rw [him] at hz
    simp only [Complex.zero_im] at hz
    linarith
  · by_cases hright : (t : ℝ) ≤ 1 / 2
    · have hsq : 0 < (clockwiseSquareBoundary t).re := by
        rw [clockwiseSquareBoundary_right_re t (lt_of_not_ge htop) hright]
        norm_num
      have hci := clockwiseCircleAtSquarePhase_right_re_pos t (lt_of_not_ge htop) hright
      have hre : (squareCircleHomotopyLoop u).re =
          (1 - s) * (clockwiseSquareBoundary t).re +
            s * (clockwiseCircleAtSquarePhase t).re := by
        simp [squareCircleHomotopyLoop, squareCircleHomotopy, s, t,
          Complex.add_re, Complex.real_smul]
      have hmix := convexCombination_pos hsq hci hs0 hs1
      have hz := congrArg Complex.re (hz0)
      rw [hre] at hz
      simp only [Complex.zero_re] at hz
      linarith
    · by_cases hbottom : (t : ℝ) ≤ 3 / 4
      · have hsq : 0 < -(clockwiseSquareBoundary t).im := by
          rw [clockwiseSquareBoundary_bottom_im t (lt_of_not_ge hright) hbottom]
          norm_num
        have hci : 0 < -(clockwiseCircleAtSquarePhase t).im := by
          have h := clockwiseCircleAtSquarePhase_bottom_im_neg t (lt_of_not_ge hright) hbottom
          linarith
        have himneg : -(squareCircleHomotopyLoop u).im =
            (1 - s) * (-(clockwiseSquareBoundary t).im) +
              s * (-(clockwiseCircleAtSquarePhase t).im) := by
          rw [him]; ring
        have hmix := convexCombination_pos hsq hci hs0 hs1
        have hz := congrArg Complex.im hz0
        have hzneg : -(squareCircleHomotopyLoop u).im = 0 := by rw [hz]; simp
        rw [himneg] at hzneg
        linarith
      · have hsq : 0 < -(clockwiseSquareBoundary t).re := by
          rw [clockwiseSquareBoundary_left_re t (lt_of_not_ge hbottom)]
          norm_num
        have hci : 0 < -(clockwiseCircleAtSquarePhase t).re := by
          have h := clockwiseCircleAtSquarePhase_left_re_neg t (lt_of_not_ge hbottom)
          linarith
        have hereneg : -(squareCircleHomotopyLoop u).re =
            (1 - s) * (-(clockwiseSquareBoundary t).re) +
              s * (-(clockwiseCircleAtSquarePhase t).re) := by
          have hre : (squareCircleHomotopyLoop u).re =
              (1 - s) * (clockwiseSquareBoundary t).re +
                s * (clockwiseCircleAtSquarePhase t).re := by
            simp [squareCircleHomotopyLoop, squareCircleHomotopy, s, t,
              Complex.add_re, Complex.real_smul]
          rw [hre]; ring
        have hmix := convexCombination_pos hsq hci hs0 hs1
        have hz := congrArg Complex.re hz0
        have hzneg : -(squareCircleHomotopyLoop u).re = 0 := by rw [hz]; simp
        rw [hereneg] at hzneg
        linarith
-- Diagnostic/public normalized-circle winding, before the square homotopy.
theorem windingNumber_clockwiseCircleAtSquarePhase_zero :
    windingNumber clockwiseCircleAtSquarePhase 0
      clockwiseCircleAtSquarePhase_avoids_zero = -1 := by
  apply Circle.degree_eq_of_sub_eq
    (θ := fun t => 3 * Real.pi / 4 - 2 * Real.pi * t)
  · fun_prop
  · intro t
    apply Subtype.ext
    rw [normalizedLoop_coe_apply]
    simp only [clockwiseCircleAtSquarePhase_apply,
      sub_zero, Circle.norm_coe, Complex.ofReal_one, div_one]
  · simp

theorem windingNumber_clockwiseSquareBoundary_zero :
    windingNumber clockwiseSquareBoundary 0 clockwiseSquareBoundary_avoids_zero = -1 := by
  have h0 : ∀ t : I, squareCircleHomotopy (0, t) = clockwiseSquareBoundary t := by
    intro t
    simp [squareCircleHomotopy]
  have h1 : ∀ t : I, squareCircleHomotopy (1, t) = clockwiseCircleAtSquarePhase t := by
    intro t
    simp [squareCircleHomotopy]
  have hF : ∀ s : I, squareCircleHomotopy (s, 0) = squareCircleHomotopy (s, 1) := by
    intro s
    have hsq : clockwiseSquareBoundary 0 = clockwiseSquareBoundary 1 := by
      rw [clockwiseSquareBoundary.source, clockwiseSquareBoundary.target]
    have hci : clockwiseCircleAtSquarePhase 0 = clockwiseCircleAtSquarePhase 1 := by
      rw [clockwiseCircleAtSquarePhase.source, clockwiseCircleAtSquarePhase.target]
    change (1 - (s : ℝ)) • clockwiseSquareBoundary 0 +
        (s : ℝ) • clockwiseCircleAtSquarePhase 0 =
      (1 - (s : ℝ)) • clockwiseSquareBoundary 1 +
        (s : ℝ) • clockwiseCircleAtSquarePhase 1
    exact congrArg₂ (fun a b : ℂ => (1 - (s : ℝ)) • a + (s : ℝ) • b) hsq hci
  exact (windingNumber_eq_of_homotopy clockwiseSquareBoundary clockwiseCircleAtSquarePhase
      0 clockwiseSquareBoundary_avoids_zero clockwiseCircleAtSquarePhase_avoids_zero
      squareCircleHomotopy h0 h1 hF squareCircleHomotopy_avoids_zero).trans
    windingNumber_clockwiseCircleAtSquarePhase_zero

end
end PottsContinuity.FKC.Curves
