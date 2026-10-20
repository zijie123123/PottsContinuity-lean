module

public import PottsContinuity.BD12.KSTArmCoverDualLimit
public import PottsContinuity.BD12.WholePlaneDuality
public import PottsContinuity.Foundations.EveryExhaustion

/-! The exact KST arm bound for both actual FK boundary limits at the explicit
self-dual parameter. Genuine threshold identification is a separate result. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.Duality

/-- Wired KST first-relation (ii), with the exact source transform at scale 64k. -/
theorem wired_kst_arm_cover_lower_bound_selfDual (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (k : ℕ) (hk : 1 ≤ k) :
    kstCoverTransform (μ.real (horizontalRectangle (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k))) ≤
      μ.real (kstArm (64*k)) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨ν, hν⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (criticalParameters q).toP (criticalParameters q).toQ (criticalParameters q).property 0
  exact kst_arm_cover_lower_bound_of_dualLimit (criticalParameters q) 0 μ ν hν
    (wired_limit_map_dual_selfDual q ν μ hν hμ) k hk

end PottsContinuity.BD12
