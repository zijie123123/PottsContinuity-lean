module

public import PottsContinuity.BD12.FiniteSeedWindow

/-! Measurability of the actual fixed-prefix seed law, including its dependence
on the prescribed original inputs. This is needed for prefix disintegration. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Products of measurable probability-valued kernels are measurable. -/
theorem probabilityKernel_prod_measurable {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (K : Ω → Measure α) (L : Ω → Measure β)
    [∀ x, IsProbabilityMeasure (K x)] [∀ x, IsProbabilityMeasure (L x)]
    (hK : Measurable K) (hL : Measurable L) :
    Measurable (fun x => (K x).prod (L x)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_prod.symm isPiSystem_prod
  rintro _ ⟨s, hs, t, ht, rfl⟩
  simp only [Measure.prod_prod]
  exact ((Measure.measurable_coe hs).comp hK).mul ((Measure.measurable_coe ht).comp hL)

/-- Push a measurable probability kernel through a jointly measurable map. -/
theorem probabilityKernel_param_map_measurable {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (K : Ω → Measure α)
    [∀ x, IsProbabilityMeasure (K x)] (hK : Measurable K)
    (F : Ω × α → β) (hF : Measurable F) :
    Measurable (fun x => (K x).map (fun a => F (x, a))) := by
  have hp := probabilityKernel_prod_measurable (fun x : Ω => Measure.dirac x) K
    Measure.measurable_dirac hK
  have h := (Measure.measurable_map F hF).comp hp
  simpa only [Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left, Function.comp_def] using h

theorem finiteHybridAuxLaw_fixedU_measurable (fixedThrough i : ℕ) :
    Measurable (fun U : ℕ → ℝ => finiteHybridAuxLaw fixedThrough U i) := by
  unfold finiteHybridAuxLaw
  split_ifs
  · exact Measure.measurable_dirac.comp (measurable_pi_apply i)
  · exact measurable_const

/-- The fixed original prefix is a genuine measurable kernel parameter. -/
theorem finiteHybridSeedWindow_fixedU_measurable (fixedThrough : ℕ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ) :
    Measurable (fun U : ℕ → ℝ => finiteHybridSeedWindow fixedThrough U background start n) := by
  induction n generalizing start with
  | zero => exact measurable_const
  | succ n ih =>
    exact (Measure.measurable_map _ (measurable_stream_update start)).comp
      (probabilityKernel_prod_measurable _ _
        (probabilityKernel_prod_measurable _ _
          (finiteHybridAuxLaw_fixedU_measurable fixedThrough start) measurable_const)
        (ih (start + 1)))

end
end PottsContinuity.BD12
