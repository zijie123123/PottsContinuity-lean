module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Linear integration of a four-term identity on an almost-everywhere fibre. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- Integrate a four-term identity, with integrability required only for its
four components. The identity itself may hold only almost everywhere. -/
theorem integral_four_term_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x a b c d : Ω → ℝ)
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) (hd : Integrable d μ)
    (h : ∀ᵐ z ∂μ, x z = a z + b z - c z - d z) :
    (∫ z, x z ∂μ) = (∫ z, a z ∂μ) + (∫ z, b z ∂μ) -
      (∫ z, c z ∂μ) - (∫ z, d z ∂μ) := by
  calc
    _ = ∫ z, a z + b z - c z - d z ∂μ := integral_congr_ae h
    _ = _ := by
      rw [integral_sub (f := fun z => a z + b z - c z) (g := d) ((ha.add hb).sub hc) hd,
        integral_sub (f := fun z => a z + b z) (g := c) (ha.add hb) hc,
        integral_add (f := a) (g := b) ha hb]

end PottsContinuity.BD12
