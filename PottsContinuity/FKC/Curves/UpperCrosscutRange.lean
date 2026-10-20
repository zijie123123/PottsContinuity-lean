-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/UpperCrosscutRange.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.UpperCrosscutWinding
public import PottsContinuity.FKC.Curves.WindingHalfPlane
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval
noncomputable section

def upperCrosscutBox (N : ℝ) : Set ℂ :=
  {z | -N ≤ z.re ∧ z.re ≤ N ∧ -1 ≤ z.im ∧ z.im ≤ N}

private theorem convex_upperCrosscutBox (N : ℝ) : Convex ℝ (upperCrosscutBox N) := by
  have hset : upperCrosscutBox N =
      ({z : ℂ | -N ≤ z.re} ∩ {z | z.re ≤ N} ∩
        {z | -1 ≤ z.im} ∩ {z | z.im ≤ N}) := by
    ext z
    simp [upperCrosscutBox, and_assoc]
  rw [hset]
  exact (((convex_halfSpace_ge Complex.reLm.isLinear (-N)).inter
      (convex_halfSpace_le Complex.reLm.isLinear N)).inter
    (convex_halfSpace_ge Complex.imLm.isLinear (-1))).inter
      (convex_halfSpace_le Complex.imLm.isLinear N)

private theorem upperCrosscutBox_mem_top {N : ℝ} (_hN : 0 ≤ N) {z : ℂ}
    (h : -N ≤ z.re ∧ z.re ≤ N ∧ 0 ≤ z.im ∧ z.im ≤ N) :
    z ∈ upperCrosscutBox N := by
  exact ⟨h.1, h.2.1, by linarith [h.2.2.1], h.2.2.2⟩

private theorem upperCrosscutBox_mem_lower_endpoint {N : ℝ} {z : ℂ}
    (hx : -N ≤ z.re ∧ z.re ≤ N) (hz : z.im = 0) (_hN : 0 ≤ N) :
    z - Complex.I ∈ upperCrosscutBox N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Complex.sub_re] using hx.1
  · simpa [Complex.sub_re] using hx.2
  · simp [Complex.sub_im, hz]
  · simp [Complex.sub_im, hz]
    linarith

theorem upperCrosscutClosure_range_subset {a b : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N) :
    range (upperCrosscutClosure top) ⊆ upperCrosscutBox N := by
  have hend : (-N ≤ a.re ∧ a.re ≤ N) ∧ (-N ≤ b.re ∧ b.re ≤ N) := by
    constructor
    · simpa only [Path.source] using
        (show -N ≤ (top 0).re ∧ (top 0).re ≤ N from ⟨(htop 0).1, (htop 0).2.1⟩)
    · simpa only [Path.target] using
        (show -N ≤ (top 1).re ∧ (top 1).re ≤ N from ⟨(htop 1).1, (htop 1).2.1⟩)
  rcases hend with ⟨⟨ha_lo, ha_hi⟩, ⟨hb_lo, hb_hi⟩⟩
  have haBox : a ∈ upperCrosscutBox N :=
    upperCrosscutBox_mem_top hN ⟨ha_lo, ha_hi, by simp [ha_im], by linarith⟩
  have hbBox : b ∈ upperCrosscutBox N :=
    upperCrosscutBox_mem_top hN ⟨hb_lo, hb_hi, by simp [hb_im], by linarith⟩
  have haLowerBox : a - Complex.I ∈ upperCrosscutBox N :=
    upperCrosscutBox_mem_lower_endpoint ⟨ha_lo, ha_hi⟩ ha_im hN
  have hbLowerBox : b - Complex.I ∈ upperCrosscutBox N :=
    upperCrosscutBox_mem_lower_endpoint ⟨hb_lo, hb_hi⟩ hb_im hN
  have hconv := convex_upperCrosscutBox N
  have htopBox : range top ⊆ upperCrosscutBox N := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact upperCrosscutBox_mem_top hN (htop t)
  have hright : range (upperCrosscutRight : Path b (b - Complex.I)) ⊆
      upperCrosscutBox N := by
    rintro z ⟨t, rfl⟩
    change AffineMap.lineMap b (b - Complex.I) (t : ℝ) ∈ upperCrosscutBox N
    exact hconv.lineMap_mem hbBox hbLowerBox t.2
  have hbottom : range (upperCrosscutBottom : Path (b - Complex.I) (a - Complex.I)) ⊆
      upperCrosscutBox N := by
    rintro z ⟨t, rfl⟩
    change AffineMap.lineMap (b - Complex.I) (a - Complex.I) (t : ℝ) ∈ upperCrosscutBox N
    exact hconv.lineMap_mem hbLowerBox haLowerBox t.2
  have hleft : range (upperCrosscutLeft : Path (a - Complex.I) a) ⊆
      upperCrosscutBox N := by
    rintro z ⟨t, rfl⟩
    change AffineMap.lineMap (a - Complex.I) a (t : ℝ) ∈ upperCrosscutBox N
    exact hconv.lineMap_mem haLowerBox haBox t.2
  change range (((top.trans upperCrosscutRight).trans
    (upperCrosscutBottom.trans upperCrosscutLeft))) ⊆ upperCrosscutBox N
  rw [Path.trans_range, Path.trans_range, Path.trans_range]
  exact union_subset (union_subset htopBox hright) (union_subset hbottom hleft)

theorem windingNumber_upperCrosscutClosure_eq_zero_of_re_lt_left
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (hz : z.re < -N) :
    windingNumber (upperCrosscutClosure top) z (by
      intro h
      have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
      linarith [hbox.1]) = 0 := by
  let c : ℝ := (z.re + -N) / 2
  have hzc : z.re ≤ c := by dsimp [c]; linarith
  have hpath : ∀ t, c < (upperCrosscutClosure top t).re := by
    intro t
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop ⟨t, rfl⟩
    dsimp [upperCrosscutBox] at hbox
    dsimp [c]
    linarith [hbox.1]
  exact windingNumber_eq_zero_of_range_re_gt (upperCrosscutClosure top) c hpath hzc

theorem windingNumber_upperCrosscutClosure_eq_zero_of_re_gt_right
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (hz : N < z.re) :
    windingNumber (upperCrosscutClosure top) z (by
      intro h
      have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
      linarith [hbox.2.1]) = 0 := by
  let c : ℝ := (N + z.re) / 2
  have hzc : c ≤ z.re := by dsimp [c]; linarith
  have hpath : ∀ t, (upperCrosscutClosure top t).re < c := by
    intro t
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop ⟨t, rfl⟩
    dsimp [upperCrosscutBox] at hbox
    dsimp [c]
    linarith [hbox.2.1]
  exact windingNumber_eq_zero_of_range_re_lt (upperCrosscutClosure top) c hpath hzc

theorem windingNumber_upperCrosscutClosure_eq_zero_of_im_gt
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (hz : N < z.im) :
    windingNumber (upperCrosscutClosure top) z (by
      intro h
      have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
      linarith [hbox.2.2.2]) = 0 := by
  let c : ℝ := (N + z.im) / 2
  have hzc : c ≤ z.im := by dsimp [c]; linarith
  have hpath : ∀ t, (upperCrosscutClosure top t).im < c := by
    intro t
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop ⟨t, rfl⟩
    dsimp [upperCrosscutBox] at hbox
    dsimp [c]
    linarith [hbox.2.2.2]
  exact windingNumber_eq_zero_of_range_im_lt (upperCrosscutClosure top) c hpath hzc

end
end PottsContinuity.FKC.Curves
