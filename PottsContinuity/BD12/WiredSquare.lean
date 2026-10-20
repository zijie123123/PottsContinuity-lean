module

public import PottsContinuity.BD12.WholePlaneRectangleDuality
public import PottsContinuity.BD12.RectangleSymmetry
public import PottsContinuity.Infinite.LocalComparisons
public import PottsContinuity.PD.RCInfinite.TranslationSupport
public import PottsContinuity.Foundations.EveryExhaustion

/-!
# Wired square crossing bound at the self-dual formula

Whole-plane duality, free-to-wired comparison and an affine diagonal symmetry
give the lower bound without symmetric mixed-boundary domains or torus laws.
-/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

theorem free_limit_le_wired_cylinder (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ₁)
    {A : Set LatticeConfiguration} (hA : IsCylinder A) (hupper : IsUpperSet A) :
    μ₀.real A ≤ μ₁.real A := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨m, hm⟩ := (eventually_finset_in_box F).exists
  exact Infinite.free_limit_le_wired_limit_local θ μ₀ μ₁
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₀)
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₁)
    m ⟨F, hF⟩ (hF.mono hm) hupper

theorem dualPortRectangle_isUpperSet (a : LatticeVertex) (w h : ℕ) :
    IsUpperSet (dualPortRectangle a w h) := by
  rintro ω η hωη ⟨b, hb, t, ht, hbt⟩
  exact ⟨b, hb, t, ht, actualConnected_mono
    (embeddedRestriction_monotone _ _ hωη) hbt⟩

/-- For any free/wired pair at p_sd, the wired (n+1)-by-n actual horizontal
crossing has probability at least one half, including n=0. -/
theorem wired_square_crossing_ge_half_of_pair (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ₁)
    (a : LatticeVertex) (n : ℕ) :
    (1 / 2 : ℝ) ≤ μ₁.real (horizontalRectangle a (n + 1) n) := by
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  have hcomp : μ₁.real ((horizontalRectangle a (n + 1) n)ᶜ) =
      μ₀.real (dualPortRectangle a (n + 1) n) :=
    congrArg ENNReal.toReal
      (wired_horizontal_compl_eq_free_dualPort q μ₀ μ₁ hμ₀ hμ₁ a (n + 1) n)
  have hdom := free_limit_le_wired_cylinder (criticalParameters q) μ₀ μ₁ hμ₀ hμ₁
    (dualPortRectangle_isCylinder a (n + 1) n) (dualPortRectangle_isUpperSet a (n + 1) n)
  have hstrip : μ₁.real (dualPortRectangle a (n + 1) n) ≤
      μ₁.real (verticalRectangle (a.1, a.2 - 1) n (n + 1)) :=
    measureReal_mono (dualPortRectangle_subset_vertical a n n)
  have hsym : μ₁.real (verticalRectangle (a.1, a.2 - 1) n (n + 1)) ≤
      μ₁.real (horizontalRectangle a (n + 1) n) :=
    ENNReal.toReal_mono (measure_ne_top μ₁ _)
      (wired_vertical_strip_le_horizontal (criticalParameters q) μ₁ hμ₁ a n n)
  rw [probReal_compl_eq_one_sub
    (horizontalRectangle_isCylinder a (n + 1) n).measurableSet] at hcomp
  linarith

/-- Every wired every-exhaustion limit at the self-dual formula has the square
crossing bound. The free limit needed by duality exists by Foundations. -/
theorem wired_square_crossing_ge_half (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ)
    (a : LatticeVertex) (n : ℕ) :
    (1 / 2 : ℝ) ≤ μ.real (horizontalRectangle a (n + 1) n) := by
  obtain ⟨μ₀, hμ₀⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (criticalParameters q).toP (criticalParameters q).toQ (criticalParameters q).property 0
  exact wired_square_crossing_ge_half_of_pair q μ₀ μ hμ₀ hμ a n

end PottsContinuity.BD12
