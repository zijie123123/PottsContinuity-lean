module

public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.BD12.WholePlaneDuality
public import PottsContinuity.PD.Duality.ScreenBridge
public import PottsContinuity.Thm3.Prop4.ArmMonotone
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Whole-plane dual arms for the corrected Proposition 4 proof

The actual complementary-dual transform exchanges the frozen wired and free
limits at the explicit self-dual parameter. Face labels denote centers shifted
by (1/2,1/2); original-edge states and the exact frozen arm event are retained.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK.Medial

/-- The S4 infinite-volume duality step, with both frozen limit predicates. -/
theorem selfDual_wired_dual_measure_eq_free (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁) :
    μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ :=
  BD12.wired_limit_map_dual_selfDual q μ₀ μ₁ hμ₀ hμ₁

/-- Exact event probabilities, without a cylinder or finite-event restriction. -/
theorem selfDual_wired_dual_event_probability_eq_free (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁)
    (E : Set PD.FK.LatticeConfiguration) (hE : MeasurableSet E) :
    μ₁.real (wholePlaneDualConfigurationHomeomorph ⁻¹' E) = μ₀.real E := by
  have h := congrArg (fun ν : Measure PD.FK.LatticeConfiguration => ν E)
    (selfDual_wired_dual_measure_eq_free q μ₀ μ₁ hμ₀ hμ₁)
  rw [Measure.map_apply (μ := μ₁) wholePlaneDualConfigurationHomeomorph_measurable hE] at h
  exact congrArg ENNReal.toReal h

/-- Whole-plane dual open connections are exactly frozen primal connections of the dual sample. -/
theorem closedDualGraph_eq_frozen_dualOpenGraph (ω : PD.FK.LatticeConfiguration) :
    wholePlaneClosedDualGraph ω = rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω) := by
  exact (wholePlaneOpenPrimalGraph_dualConfiguration_eq ω).symm.trans
    (PD.Duality.wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph _)

/-- The wired partner exists uniquely and has exactly the prescribed frozen free dual law. -/
theorem existsUnique_wired_dual_of_selfDual_free_limit (q : Set.Ici (1 : ℝ))
    (μ₀ : Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀) :
    ∃! μ₁ : Measure PD.FK.LatticeConfiguration,
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
        (RSW.selfDualParameters q).toQ 1 μ₁ ∧
      μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ := by
  obtain ⟨μ₁,hμ₁⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ
    (RSW.selfDualParameters q).property 1
  refine ⟨μ₁,⟨hμ₁,selfDual_wired_dual_measure_eq_free q μ₀ μ₁ hμ₀ hμ₁⟩,?_⟩
  intro ν hν
  exact WellDefined.limit_unique _ _ 1 ν μ₁ hν.1 hμ₁

end PottsContinuity.Thm3.Prop4
