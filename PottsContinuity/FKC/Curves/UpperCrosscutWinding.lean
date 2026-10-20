-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/UpperCrosscutWinding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.FourStripWinding
public import PottsContinuity.FKC.Curves.WindingTranslation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval
noncomputable section

def upperCrosscutRight {b : ℂ} : Path b (b - Complex.I) :=
  Path.segment b (b - Complex.I)

def upperCrosscutBottom {a b : ℂ} : Path (b - Complex.I) (a - Complex.I) :=
  Path.segment (b - Complex.I) (a - Complex.I)

def upperCrosscutLeft {a : ℂ} : Path (a - Complex.I) a :=
  Path.segment (a - Complex.I) a

def upperCrosscutClosure {a b : ℂ} (top : Path a b) : Path a a :=
  balancedFourPath top upperCrosscutRight upperCrosscutBottom upperCrosscutLeft

private theorem upperCrosscut_map_balanced {a b : ℂ} (top : Path a b)
    (f : C(ℂ, ℂ)) :
    (upperCrosscutClosure top).map f.continuous =
      balancedFourPath (top.map f.continuous)
        ((upperCrosscutRight).map f.continuous)
        ((upperCrosscutBottom).map f.continuous)
        ((upperCrosscutLeft).map f.continuous) := by
  simp only [upperCrosscutClosure, balancedFourPath]
  rw [Path.map_trans, Path.map_trans, Path.map_trans]

private theorem upperCrosscut_right_re (b : ℂ) (t : I) :
    (Path.segment b (b - Complex.I) t).re = b.re := by
  change (AffineMap.lineMap b (b - Complex.I) (t : ℝ)).re = b.re
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.mul_re, Complex.real_smul, Complex.ofReal_re,
    Complex.sub_re, Complex.I_re, Complex.ofReal_im]
  ring

private theorem upperCrosscut_left_re (a : ℂ) (t : I) :
    (Path.segment (a - Complex.I) a t).re = a.re := by
  change (AffineMap.lineMap (a - Complex.I) a (t : ℝ)).re = a.re
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_re, Complex.mul_re, Complex.real_smul, Complex.ofReal_re,
    Complex.sub_re, Complex.I_re, Complex.ofReal_im]
  ring

private theorem upperCrosscut_bottom_im {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0)
    (t : I) :
    (Path.segment (b - Complex.I) (a - Complex.I) t).im = -1 := by
  change (AffineMap.lineMap (b - Complex.I) (a - Complex.I) (t : ℝ)).im = -1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.add_im, Complex.mul_im, Complex.real_smul, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, Complex.I_im, zero_mul]
  rw [ha, hb]
  ring


/-- The branch point between the real axis and the lower closing segment. -/
def upperCrosscutBranchCenter : ℂ := (1 / 2 : ℝ) - (1 / 2 : ℝ) * Complex.I

def upperCrosscutShift : C(ℂ, ℂ) :=
  ⟨fun z => z - upperCrosscutBranchCenter,
    continuous_id.sub (continuous_const : Continuous (fun _ : ℂ => upperCrosscutBranchCenter))⟩

def upperCrosscutShiftedTop {a b : ℂ} (top : Path a b) :=
  top.map upperCrosscutShift.continuous

def upperCrosscutShiftedRight {b : ℂ} :=
  (upperCrosscutRight : Path b (b - Complex.I)).map upperCrosscutShift.continuous

def upperCrosscutShiftedBottom {a b : ℂ} :=
  (upperCrosscutBottom : Path (b - Complex.I) (a - Complex.I)).map
    upperCrosscutShift.continuous

def upperCrosscutShiftedLeft {a : ℂ} :=
  (upperCrosscutLeft : Path (a - Complex.I) a).map upperCrosscutShift.continuous

theorem upperCrosscutTranslatedSigns {a b : ℂ} (top : Path a b)
    (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, 0 ≤ (top t).im) :
    (∀ t, 0 < (upperCrosscutShiftedTop top t).im) ∧
    (∀ t, 0 < (upperCrosscutShiftedRight (b := b) t).re) ∧
    (∀ t, (upperCrosscutShiftedBottom (a := a) (b := b) t).im < 0) ∧
    (∀ t, (upperCrosscutShiftedLeft (a := a) t).re < 0) := by
  have hc_re : upperCrosscutBranchCenter.re = 1 / 2 := by
    norm_num [upperCrosscutBranchCenter]
  have hc_im : upperCrosscutBranchCenter.im = -(1 / 2) := by
    norm_num [upperCrosscutBranchCenter]
  have htop' : ∀ t, 0 < (upperCrosscutShiftedTop top t).im := by
    intro t
    change 0 < (top t - upperCrosscutBranchCenter).im
    rw [Complex.sub_im, hc_im]
    simp only [sub_neg_eq_add]
    linarith [htop t]
  have hright' : ∀ t, 0 < (upperCrosscutShiftedRight (b := b) t).re := by
    intro t
    change 0 < ((Path.segment b (b - Complex.I) t) - upperCrosscutBranchCenter).re
    rw [Complex.sub_re, upperCrosscut_right_re, hc_re]
    linarith [hb_re]
  have hbottom' : ∀ t, (upperCrosscutShiftedBottom (a := a) (b := b) t).im < 0 := by
    intro t
    change ((Path.segment (b - Complex.I) (a - Complex.I) t) - upperCrosscutBranchCenter).im < 0
    rw [Complex.sub_im, upperCrosscut_bottom_im ha_im hb_im, hc_im]
    norm_num
  have hleft' : ∀ t, (upperCrosscutShiftedLeft (a := a) t).re < 0 := by
    intro t
    change ((Path.segment (a - Complex.I) a t) - upperCrosscutBranchCenter).re < 0
    rw [Complex.sub_re, upperCrosscut_left_re, hc_re]
    linarith [ha_re]
  exact ⟨htop', hright', hbottom', hleft'⟩

private theorem upperCrosscut_map_branchCenter {a b : ℂ} (top : Path a b) :
    translateLoop (upperCrosscutClosure top) upperCrosscutBranchCenter =
      balancedFourPath (upperCrosscutShiftedTop top)
        (upperCrosscutShiftedRight (b := b))
        (upperCrosscutShiftedBottom (a := a) (b := b))
        (upperCrosscutShiftedLeft (a := a)) := by
  change (upperCrosscutClosure top).map upperCrosscutShift.continuous = _
  exact upperCrosscut_map_balanced top upperCrosscutShift

theorem upperCrosscutClosure_avoids_branchCenter {a b : ℂ} (top : Path a b)
    (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, 0 ≤ (top t).im) :
    upperCrosscutBranchCenter ∉ range (upperCrosscutClosure top) := by
  rcases upperCrosscutTranslatedSigns top ha_im hb_im ha_re hb_re htop with
    ⟨htop', hright', hbottom', hleft'⟩
  have hshift : (0 : ℂ) ∉ range
      (balancedFourPath (upperCrosscutShiftedTop top)
        (upperCrosscutShiftedRight (b := b))
        (upperCrosscutShiftedBottom (a := a) (b := b))
        (upperCrosscutShiftedLeft (a := a))) :=
    balancedFourPath_avoids_zero _ _ _ _ htop' hright' hbottom' hleft'
  have hzero : (0 : ℂ) ∉ range
      (translateLoop (upperCrosscutClosure top) upperCrosscutBranchCenter) := by
    rw [upperCrosscut_map_branchCenter]
    exact hshift
  intro h
  apply hzero
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simp [translateLoop_apply, ht]

private theorem windingNumber_eq_of_path_eq {a z : ℂ} (γ γ' : Path a a)
    (hz : z ∉ range γ) (hz' : z ∉ range γ') (h : γ = γ') :
    windingNumber γ z hz = windingNumber γ' z hz' := by
  cases h
  rfl

theorem upperCrosscutClosure_winding {a b : ℂ} (top : Path a b)
    (ha_im : a.im = 0) (hb_im : b.im = 0)
    (ha_re : a.re ≤ 0) (hb_re : 1 ≤ b.re)
    (htop : ∀ t, 0 ≤ (top t).im) :
    windingNumber (upperCrosscutClosure top) upperCrosscutBranchCenter
      (upperCrosscutClosure_avoids_branchCenter top ha_im hb_im ha_re hb_re htop) = -1 := by
  rcases upperCrosscutTranslatedSigns top ha_im hb_im ha_re hb_re htop with
    ⟨htop', hright', hbottom', hleft'⟩
  have hwind' := windingNumber_balancedFourPath_zero
    (upperCrosscutShiftedTop top)
    (upperCrosscutShiftedRight (b := b))
    (upperCrosscutShiftedBottom (a := a) (b := b))
    (upperCrosscutShiftedLeft (a := a)) htop' hright' hbottom' hleft'
  have hzero : (0 : ℂ) ∉ range
      (translateLoop (upperCrosscutClosure top) upperCrosscutBranchCenter) := by
    rw [upperCrosscut_map_branchCenter]
    exact balancedFourPath_avoids_zero _ _ _ _ htop' hright' hbottom' hleft'
  have hshift : (0 : ℂ) ∉ range
      (balancedFourPath (upperCrosscutShiftedTop top)
        (upperCrosscutShiftedRight (b := b))
        (upperCrosscutShiftedBottom (a := a) (b := b))
        (upperCrosscutShiftedLeft (a := a))) :=
    balancedFourPath_avoids_zero _ _ _ _ htop' hright' hbottom' hleft'
  have hwindmap := windingNumber_eq_of_path_eq
    (translateLoop (upperCrosscutClosure top) upperCrosscutBranchCenter)
    (balancedFourPath (upperCrosscutShiftedTop top)
      (upperCrosscutShiftedRight (b := b))
      (upperCrosscutShiftedBottom (a := a) (b := b))
      (upperCrosscutShiftedLeft (a := a))) hzero hshift
    (upperCrosscut_map_branchCenter top)
  have htrans := windingNumber_translateLoop (upperCrosscutClosure top)
    (upperCrosscutClosure_avoids_branchCenter top ha_im hb_im ha_re hb_re htop)
    (c := upperCrosscutBranchCenter)
  calc
    windingNumber (upperCrosscutClosure top) upperCrosscutBranchCenter
        (upperCrosscutClosure_avoids_branchCenter top ha_im hb_im ha_re hb_re htop) =
      windingNumber (translateLoop (upperCrosscutClosure top) upperCrosscutBranchCenter)
        (upperCrosscutBranchCenter - upperCrosscutBranchCenter)
        (not_mem_range_translateLoop (upperCrosscutClosure top)
          (upperCrosscutClosure_avoids_branchCenter top ha_im hb_im ha_re hb_re htop)) := htrans.symm
    _ = -1 := by
      simpa [upperCrosscutBranchCenter, sub_self] using hwindmap.trans hwind'


end
end PottsContinuity.FKC.Curves
