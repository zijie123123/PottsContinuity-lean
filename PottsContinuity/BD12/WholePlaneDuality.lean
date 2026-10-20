module

public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.Duality.ReverseInfiniteDuality

/-!
# Whole-plane duality with every-exhaustion hypotheses

These statements consume the frozen limit predicate, using its box
specialization only inside the proof. The self-dual parameter is the explicit
value √q/(1+√q) of `criticalParameters q`; it is the critical point by
`BD12.isRCCriticalPoint_selfDual` in `BD12.CriticalValue`.
-/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK PD.FK.Medial PD.Duality

/-- Actual free-to-wired dual transport for frozen every-exhaustion limits. -/
theorem free_limit_map_dual (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₀.map wholePlaneDualConfigurationHomeomorph = μ₁ := by
  exact free_map_dual_eq_wired θ μ₀ μ₁
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₀)
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₁)

/-- Actual wired-to-free dual transport for frozen every-exhaustion limits. -/
theorem wired_limit_map_dual (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ := by
  exact wired_map_dual_eq_free θ μ₀ μ₁
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₀)
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ₁)

/-- At p_sd the wired law maps to the free law with unchanged parameters. -/
theorem wired_limit_map_dual_selfDual (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ₁) :
    μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ := by
  apply wired_limit_map_dual (criticalParameters q) μ₀ μ₁ hμ₀
  simpa only [dualParameters_criticalParameters] using hμ₁

end PottsContinuity.BD12
