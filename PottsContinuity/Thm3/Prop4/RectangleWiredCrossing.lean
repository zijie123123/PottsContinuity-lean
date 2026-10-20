module

public import PottsContinuity.Thm3.Prop4.RectangleNoncrossingEscape
public import PottsContinuity.Thm3.Prop4.DualEscapeTail

/-!
# Actual wired-plane rectangle crossings from the free arm bound

Finite noncrossing forces a genuine complementary dual arm from one of w
bottom face roots. Whole-plane self-duality then gives an all-q probability
bound with the original stretched-exponential coefficient retained.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial

/-- No mixed-boundary or exploration premise is needed for the wired-plane rectangle error. -/
theorem selfDual_wired_rectangle_noncrossing_le_stretched (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ n : ℕ, 1 ≤ n → RSW.oneArmProbability μ₀ n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (a : ℤ × ℤ) (w h : ℕ) :
    μ₁.real (BD12.horizontalRectangle a w h)ᶜ ≤
      (w : ℝ)*Real.exp (-c₀*((h : ℝ)+1)^α) := by
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  have hbound := selfDual_wired_dual_square_escape_union_le q μ₀ μ₁ hμ₀ hμ₁
    c₀ α hc₀ hα hdecay (rectangleBottomDualRoots a w) ((h : ℝ)+1)
    (by have := Nat.cast_nonneg (α := ℝ) h; linarith only [this])
  apply le_trans _ (hbound.trans (mul_le_mul_of_nonneg_right
    (show ((rectangleBottomDualRoots a w).card : ℝ) ≤ w by
      exact_mod_cast rectangleBottomDualRoots_card_le a w) (Real.exp_nonneg _)))
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨s,hs,t,hd,p,_⟩ := rectangle_noncrossing_original_dual_escape a w h ω hω
  exact ⟨s,hs,t,by exact_mod_cast hd,⟨p⟩⟩

end PottsContinuity.Thm3.Prop4
