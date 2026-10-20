-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/FourStripWinding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.SquareBoundaryWinding

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval

noncomputable section

def balancedFourPath {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) : Path a a :=
  ((top.trans right).trans (bottom.trans left))

lemma balancedFourPath_top_mem {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) (htop : ∀ t, 0 < (top t).im)
    (t : I) (ht : (t : ℝ) ≤ 1 / 4) :
    0 < (balancedFourPath top right bottom left t).im := by
  rw [balancedFourPath, Path.trans_apply]
  have houter : (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_left houter, Path.trans_apply]
  have hinner : 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_left hinner]
  let u : I := ⟨4 * (t : ℝ), ⟨by nlinarith [t.2.1], by linarith⟩⟩
  have h := htop u
  have harg : (⟨2 * (2 * (t : ℝ)), by nlinarith [t.2.1], by linarith⟩ : I) = u := by
    apply Subtype.ext
    ring
  rw [harg]
  exact h

lemma balancedFourPath_right_mem {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) (hright : ∀ t, 0 < (right t).re)
    (t : I) (ht₁ : 1 / 4 < (t : ℝ)) (ht₂ : (t : ℝ) ≤ 1 / 2) :
    0 < (balancedFourPath top right bottom left t).re := by
  rw [balancedFourPath, Path.trans_apply]
  have houter : (t : ℝ) ≤ 1 / 2 := ht₂
  rw [dite_eq_left houter, Path.trans_apply]
  have hinner : ¬ 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_right hinner]
  let u : I := ⟨4 * (t : ℝ) - 1, ⟨by linarith, by linarith⟩⟩
  have h := hright u
  have harg : (⟨2 * (2 * (t : ℝ)) - 1, by linarith, by linarith⟩ : I) = u := by
    apply Subtype.ext
    ring
  rw [harg]
  exact h

lemma balancedFourPath_bottom_mem {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) (hbottom : ∀ t, (bottom t).im < 0)
    (t : I) (ht₁ : 1 / 2 < (t : ℝ)) (ht₂ : (t : ℝ) ≤ 3 / 4) :
    (balancedFourPath top right bottom left t).im < 0 := by
  rw [balancedFourPath, Path.trans_apply]
  have houter : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  rw [dite_eq_right houter, Path.trans_apply]
  have hinner : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [dite_eq_left hinner]
  let u : I := ⟨4 * (t : ℝ) - 2, ⟨by linarith, by linarith⟩⟩
  have h := hbottom u
  have harg : (⟨2 * (2 * (t : ℝ) - 1), by linarith, by linarith⟩ : I) = u := by
    apply Subtype.ext
    ring
  rw [harg]
  exact h

lemma balancedFourPath_left_mem {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) (hleft : ∀ t, (left t).re < 0)
    (t : I) (ht : 3 / 4 < (t : ℝ)) :
    (balancedFourPath top right bottom left t).re < 0 := by
  rw [balancedFourPath, Path.trans_apply]
  have houter : ¬ (t : ℝ) ≤ 1 / 2 := by linarith [ht]
  rw [dite_eq_right houter, Path.trans_apply]
  have hinner : ¬ 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [dite_eq_right hinner]
  let u : I := ⟨4 * (t : ℝ) - 3, ⟨by linarith, by nlinarith [t.2.2]⟩⟩
  have h := hleft u
  have harg : (⟨2 * (2 * (t : ℝ) - 1) - 1, by linarith, by nlinarith [t.2.2]⟩ : I) = u := by
    apply Subtype.ext
    ring
  rw [harg]
  exact h

theorem balancedFourPath_avoids_zero {a b c d : ℂ}
    (top : Path a b) (right : Path b c) (bottom : Path c d) (left : Path d a)
    (htop : ∀ t, 0 < (top t).im) (hright : ∀ t, 0 < (right t).re)
    (hbottom : ∀ t, (bottom t).im < 0) (hleft : ∀ t, (left t).re < 0) :
    (0 : ℂ) ∉ range (balancedFourPath top right bottom left) := by
  rintro ⟨t, ht⟩
  by_cases h₁ : (t : ℝ) ≤ 1 / 4
  · have h := balancedFourPath_top_mem top right bottom left htop t h₁
    have hz := congrArg Complex.im ht
    simp only [Complex.zero_im] at hz
    linarith
  · by_cases h₂ : (t : ℝ) ≤ 1 / 2
    · have h := balancedFourPath_right_mem top right bottom left hright t (lt_of_not_ge h₁) h₂
      have hz := congrArg Complex.re ht
      simp only [Complex.zero_re] at hz
      linarith
    · by_cases h₃ : (t : ℝ) ≤ 3 / 4
      · have h := balancedFourPath_bottom_mem top right bottom left hbottom t
          (lt_of_not_ge h₂) h₃
        have hz := congrArg Complex.im ht
        simp only [Complex.zero_im] at hz
        linarith
      · have h := balancedFourPath_left_mem top right bottom left hleft t
          (lt_of_not_ge h₃)
        have hz := congrArg Complex.re ht
        simp only [Complex.zero_re] at hz
        linarith

def fourStripSquareHomotopy {a b c d : ℂ} (top : Path a b) (right : Path b c)
    (bottom : Path c d) (left : Path d a) : C(I × I, ℂ) where
  toFun u := (1 - (u.1 : ℝ)) • balancedFourPath top right bottom left u.2 +
    (u.1 : ℝ) • clockwiseSquareBoundary u.2
  continuous_toFun := by fun_prop


theorem balancedFourPath_homotopy_avoids_zero {a b c d : ℂ}
    (top : Path a b) (right : Path b c) (bottom : Path c d) (left : Path d a)
    (htop : ∀ t, 0 < (top t).im) (hright : ∀ t, 0 < (right t).re)
    (hbottom : ∀ t, (bottom t).im < 0) (hleft : ∀ t, (left t).re < 0)
    (u : I × I) : fourStripSquareHomotopy top right bottom left u ≠ 0 := by
  intro hz0
  let s : ℝ := u.1
  let t : I := u.2
  have hs0 : 0 ≤ s := u.1.2.1
  have hs1 : s ≤ 1 := u.1.2.2
  have him : (fourStripSquareHomotopy top right bottom left u).im =
      (1 - s) * (balancedFourPath top right bottom left t).im +
        s * (clockwiseSquareBoundary t).im := by
    simp [fourStripSquareHomotopy, balancedFourPath, s, t,
      Complex.add_im, Complex.real_smul]
  have hre : (fourStripSquareHomotopy top right bottom left u).re =
      (1 - s) * (balancedFourPath top right bottom left t).re +
        s * (clockwiseSquareBoundary t).re := by
    simp [fourStripSquareHomotopy, balancedFourPath, s, t,
      Complex.add_re, Complex.real_smul]
  by_cases h₁ : (t : ℝ) ≤ 1 / 4
  · have hp : 0 < (balancedFourPath top right bottom left t).im :=
      balancedFourPath_top_mem top right bottom left htop t h₁
    have hs : 0 < (clockwiseSquareBoundary t).im := by
      rw [clockwiseSquareBoundary_top_im t h₁]
      norm_num
    have hm := convexCombination_pos hp hs hs0 hs1
    have hz := congrArg Complex.im hz0
    rw [him] at hz
    simp only [Complex.zero_im] at hz
    linarith
  · by_cases h₂ : (t : ℝ) ≤ 1 / 2
    · have hp : 0 < (balancedFourPath top right bottom left t).re :=
        balancedFourPath_right_mem top right bottom left hright t (lt_of_not_ge h₁) h₂
      have hs : 0 < (clockwiseSquareBoundary t).re := by
        rw [clockwiseSquareBoundary_right_re t (lt_of_not_ge h₁) h₂]
        norm_num
      have hm := convexCombination_pos hp hs hs0 hs1
      have hz := congrArg Complex.re hz0
      rw [hre] at hz
      simp only [Complex.zero_re] at hz
      linarith
    · by_cases h₃ : (t : ℝ) ≤ 3 / 4
      · have hp : 0 < -(balancedFourPath top right bottom left t).im := by
          have h := balancedFourPath_bottom_mem top right bottom left hbottom t
            (lt_of_not_ge h₂) h₃
          linarith
        have hs : 0 < -(clockwiseSquareBoundary t).im := by
          rw [clockwiseSquareBoundary_bottom_im t (lt_of_not_ge h₂) h₃]
          norm_num
        have himneg : -(fourStripSquareHomotopy top right bottom left u).im =
            (1 - s) * (-(balancedFourPath top right bottom left t).im) +
              s * (-(clockwiseSquareBoundary t).im) := by rw [him]; ring
        have hm := convexCombination_pos hp hs hs0 hs1
        have hz := congrArg Complex.im hz0
        have hzneg : -(fourStripSquareHomotopy top right bottom left u).im = 0 := by
          rw [hz]
          simp
        rw [himneg] at hzneg
        linarith
      · have hp : 0 < -(balancedFourPath top right bottom left t).re := by
          have h := balancedFourPath_left_mem top right bottom left hleft t (lt_of_not_ge h₃)
          linarith
        have hs : 0 < -(clockwiseSquareBoundary t).re := by
          rw [clockwiseSquareBoundary_left_re t (lt_of_not_ge h₃)]
          norm_num
        have hereneg : -(fourStripSquareHomotopy top right bottom left u).re =
            (1 - s) * (-(balancedFourPath top right bottom left t).re) +
              s * (-(clockwiseSquareBoundary t).re) := by rw [hre]; ring
        have hm := convexCombination_pos hp hs hs0 hs1
        have hz := congrArg Complex.re hz0
        have hzneg : -(fourStripSquareHomotopy top right bottom left u).re = 0 := by
          rw [hz]
          simp
        rw [hereneg] at hzneg
        linarith

theorem windingNumber_balancedFourPath_zero {a b c d : ℂ}
    (top : Path a b) (right : Path b c) (bottom : Path c d) (left : Path d a)
    (htop : ∀ t, 0 < (top t).im) (hright : ∀ t, 0 < (right t).re)
    (hbottom : ∀ t, (bottom t).im < 0) (hleft : ∀ t, (left t).re < 0) :
    windingNumber (balancedFourPath top right bottom left) 0
      (balancedFourPath_avoids_zero top right bottom left htop hright hbottom hleft) = -1 := by
  have h0 : ∀ t : I, fourStripSquareHomotopy top right bottom left (0, t) =
      balancedFourPath top right bottom left t := by
    intro t
    simp [fourStripSquareHomotopy]
  have h1 : ∀ t : I, fourStripSquareHomotopy top right bottom left (1, t) =
      clockwiseSquareBoundary t := by
    intro t
    simp [fourStripSquareHomotopy]
  have hF : ∀ s : I, fourStripSquareHomotopy top right bottom left (s, 0) =
      fourStripSquareHomotopy top right bottom left (s, 1) := by
    intro s
    have hp : balancedFourPath top right bottom left 0 =
        balancedFourPath top right bottom left 1 := by
      change ((top.trans right).trans (bottom.trans left)) 0 =
        ((top.trans right).trans (bottom.trans left)) 1
      rw [Path.source, Path.target]
    have hs : clockwiseSquareBoundary 0 = clockwiseSquareBoundary 1 := by
      rw [clockwiseSquareBoundary.source, clockwiseSquareBoundary.target]
    change (1 - (s : ℝ)) • balancedFourPath top right bottom left 0 +
        (s : ℝ) • clockwiseSquareBoundary 0 =
      (1 - (s : ℝ)) • balancedFourPath top right bottom left 1 +
        (s : ℝ) • clockwiseSquareBoundary 1
    exact congrArg₂ (fun x y : ℂ => (1 - (s : ℝ)) • x + (s : ℝ) • y) hp hs
  exact (windingNumber_eq_of_homotopy (balancedFourPath top right bottom left)
      clockwiseSquareBoundary 0
      (balancedFourPath_avoids_zero top right bottom left htop hright hbottom hleft)
      clockwiseSquareBoundary_avoids_zero
      (fourStripSquareHomotopy top right bottom left) h0 h1 hF
      (balancedFourPath_homotopy_avoids_zero top right bottom left htop hright hbottom hleft)).trans
    windingNumber_clockwiseSquareBoundary_zero

end
end PottsContinuity.FKC.Curves
