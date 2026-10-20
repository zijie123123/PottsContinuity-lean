module

public import PottsContinuity.PlanarTopology.HalfPlaneScreenBulkLimit
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- Translation invariance, positive association, uniqueness and existence
for the actual complementary-dual law make both primal boundary components finite. -/
theorem halfPlane_finite_unit_probability_one_of_dualLaw
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : μ.map wholePlaneDualConfigurationHomeomorph = ν)
    (htranslation : ∀ a : LatticeVertex, ν.map (edgeTranslate a) = ν)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → ν A * ν B ≤ ν (A ∩ B))
    (hunique : ∀ᵐ ω ∂ν, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂ν, ω ∈ infiniteClusterEvent) :
    μ halfPlaneFiniteUnitEvent = 1 := by
  let θ := fun s : ℕ => ν.real (infiniteHit (latticeBox (0,0) s : Set LatticeVertex))
  have hθ : Tendsto θ atTop (𝓝 1) := by
    have h := ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
      (infiniteHit_box_probability_tendsto_one ν hinfinite)
    simpa only [Function.comp_def,ENNReal.toReal_one,Measure.real_def,θ] using h
  have hγ : Tendsto (fun s : ℕ => 1-Real.sqrt (1-(θ s)^2)) atTop (𝓝 1) := by
    have h : Tendsto (fun s : ℕ => 1-Real.sqrt (1-(θ s)^2)) atTop
        (𝓝 (1-Real.sqrt (1-(1:ℝ)^2))) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds.sub (hθ.pow 2)).sqrt)
    simpa only [one_pow,sub_self,Real.sqrt_zero,sub_zero] using h
  have hlower : 1 ≤ μ.real halfPlaneFiniteUnitEvent := by
    apply le_of_forall_lt
    intro b hb
    let r := (b+3)/4
    have hr : r < 1 := by dsimp [r]; linarith
    obtain ⟨s,hs⟩ := (eventually_atTop.mp ((tendsto_order.mp hγ).1 r hr))
    have hh := halfPlane_screen_lower_bound_of_dualLaw μ ν hν htranslation hFKG hunique s r (hs s le_rfl)
    dsimp [r] at hh
    linarith
  have heq : μ.real halfPlaneFiniteUnitEvent = 1 := le_antisymm measureReal_le_one hlower
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by simp)).mp
    (by simpa only [ENNReal.toReal_one,Measure.real_def] using heq)

/-- The same conclusion in almost-sure form, on the actual sampled graph. -/
theorem halfPlane_finite_unit_ae_of_dualLaw
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : μ.map wholePlaneDualConfigurationHomeomorph = ν)
    (htranslation : ∀ a : LatticeVertex, ν.map (edgeTranslate a) = ν)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → ν A * ν B ≤ ν (A ∩ B))
    (hunique : ∀ᵐ ω ∂ν, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂ν, ω ∈ infiniteClusterEvent) :
    ∀ᵐ ω ∂μ, ω ∈ halfPlaneFiniteUnitEvent := by
  have hh := halfPlane_finite_unit_probability_one_of_dualLaw μ ν hν htranslation hFKG hunique hinfinite
  exact (mem_ae_iff_prob_eq_one halfPlaneFiniteUnitEvent_measurableSet).mpr hh

end
end PottsContinuity.PlanarTopology
