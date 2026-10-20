module

public import PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers.ProbabilityConsumer

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers
open MeasureTheory Thm3.Prop4 Thm3.Touch
noncomputable section

/-- The measure argument requires a cover only almost everywhere; this is
the corrected interface when exceptional infinite layers are present. -/
theorem probability_ge_half_of_ae_cover_and_map
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    (Ψ : Ω → Ω') (hΨ : Measurable Ψ)
    (H : Set Ω) (H' : Set Ω')
    (hH : MeasurableSet H) (hH' : MeasurableSet H')
    (hcover : ∀ᵐ ω ∂μ, ω ∈ H ∨ Ψ ω ∈ H')
    (hlaw : μ.map Ψ = ν) (hequal : ν.real H' = μ.real H) :
    (1/2 : ℝ) ≤ μ.real H := by
  have hsub : Hᶜ ≤ᵐ[μ] Ψ ⁻¹' H' := by
    filter_upwards [hcover] with ω hω
    exact fun hnot => hω.resolve_left hnot
  have htransport : μ.real (Ψ ⁻¹' H') = μ.real H := by
    have he := congrArg (fun ρ : Measure Ω' => ρ H') hlaw
    rw [Measure.map_apply hΨ hH'] at he
    exact (congrArg ENNReal.toReal he).trans hequal
  have hbound : μ.real Hᶜ ≤ μ.real H := by
    rw [← htransport]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [probReal_compl_eq_one_sub hH] at hbound
  linarith

end
end PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers
