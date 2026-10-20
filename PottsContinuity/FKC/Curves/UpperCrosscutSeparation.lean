-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/UpperCrosscutSeparation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.UpperCrosscutRange
public import PottsContinuity.FKC.Curves.WindingRegions
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval
noncomputable section

private theorem path_meets_loop_of_winding_ne
    {a z₀ z₁ : ℂ} (γ : Path a a) (p : Path z₀ z₁)
    (hz₀ : z₀ ∉ range γ) (hz₁ : z₁ ∉ range γ)
    (hwind : windingNumber γ z₀ hz₀ ≠ windingNumber γ z₁ hz₁) :
    ∃ w, w ∈ range p ∧ w ∈ range γ := by
  by_contra h
  have havoid : ∀ s, p s ∉ range γ := by
    intro s hs
    apply h
    exact ⟨p s, ⟨s, rfl⟩, hs⟩
  have heq := windingNumber_eq_of_path γ hz₀ hz₁ p havoid
  exact hwind heq

theorem upperCrosscut_path_meets_of_re_lt_left
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (p : Path upperCrosscutBranchCenter z) (hz : z.re < -N) :
    ∃ w, w ∈ range p ∧ w ∈ range (upperCrosscutClosure top) := by
  let hcenter := upperCrosscutClosure_avoids_branchCenter top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hzavoid : z ∉ range (upperCrosscutClosure top) := by
    intro h
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
    linarith [hbox.1]
  have hwindCenter := upperCrosscutClosure_winding top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hwindEnd := windingNumber_upperCrosscutClosure_eq_zero_of_re_lt_left
    top N hN ha_im hb_im htop hz
  apply path_meets_loop_of_winding_ne (upperCrosscutClosure top) p hcenter hzavoid
  rw [hwindCenter, hwindEnd]
  norm_num

theorem upperCrosscut_path_meets_of_re_gt_right
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (p : Path upperCrosscutBranchCenter z) (hz : N < z.re) :
    ∃ w, w ∈ range p ∧ w ∈ range (upperCrosscutClosure top) := by
  let hcenter := upperCrosscutClosure_avoids_branchCenter top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hzavoid : z ∉ range (upperCrosscutClosure top) := by
    intro h
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
    linarith [hbox.2.1]
  have hwindCenter := upperCrosscutClosure_winding top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hwindEnd := windingNumber_upperCrosscutClosure_eq_zero_of_re_gt_right
    top N hN ha_im hb_im htop hz
  apply path_meets_loop_of_winding_ne (upperCrosscutClosure top) p hcenter hzavoid
  rw [hwindCenter, hwindEnd]
  norm_num

theorem upperCrosscut_path_meets_of_im_gt
    {a b z : ℂ} (top : Path a b) (N : ℝ)
    (hN : 0 ≤ N) (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, -N ≤ (top t).re ∧ (top t).re ≤ N ∧
      0 ≤ (top t).im ∧ (top t).im ≤ N)
    (p : Path upperCrosscutBranchCenter z) (hz : N < z.im) :
    ∃ w, w ∈ range p ∧ w ∈ range (upperCrosscutClosure top) := by
  let hcenter := upperCrosscutClosure_avoids_branchCenter top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hzavoid : z ∉ range (upperCrosscutClosure top) := by
    intro h
    have hbox := upperCrosscutClosure_range_subset top N hN ha_im hb_im htop h
    linarith [hbox.2.2.2]
  have hwindCenter := upperCrosscutClosure_winding top ha_im hb_im
    ha_re hb_re
    (fun t => (htop t).2.2.1)
  have hwindEnd := windingNumber_upperCrosscutClosure_eq_zero_of_im_gt
    top N hN ha_im hb_im htop hz
  apply path_meets_loop_of_winding_ne (upperCrosscutClosure top) p hcenter hzavoid
  rw [hwindCenter, hwindEnd]
  norm_num

end
end PottsContinuity.FKC.Curves
