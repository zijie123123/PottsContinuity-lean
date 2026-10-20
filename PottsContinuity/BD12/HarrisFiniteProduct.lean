module

public import PottsContinuity.BD12.HarrisTensorization
public import PottsContinuity.BD12.UniformThreshold
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Harris association for every finite product of real probability laws,
in particular the independent uniforms in DRT's hybrid coupling. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

theorem harris_finite_product (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ)
    (f g : (Fin n → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfm : Monotone f) (hgm : Monotone g)
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin n => μ)) *
        (∫ x, g x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∫ x, f x * g x ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero => simp [integral_unique]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hcons (z : ℝ × (Fin n → ℝ)) : e.symm z = Fin.cons z.1 z.2 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hem : Monotone e.symm := by
      intro x y hxy i
      rw [hcons x, hcons y]
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using hxy.1
      · simpa only [Fin.cons_succ] using hxy.2 j
    have hprod := harris_tensorization μ (Measure.pi (fun _ : Fin n => μ))
      (fun F G _ _ hF hG hF01 hG01 => harris_one_dimensional μ F G hF hG hF01 hG01)
      (fun F G hF hG hFm hGm hF01 hG01 => ih F G hF hG hFm hGm hF01 hG01)
      (fun z => f (e.symm z)) (fun z => g (e.symm z))
      (hf.comp e.symm.measurable) (hg.comp e.symm.measurable)
      (hfm.comp hem) (hgm.comp hem) (fun z => hf01 _) (fun z => hg01 _)
    have hF := hp.integral_comp' f
    have hG := hp.integral_comp' g
    have hFG := hp.integral_comp' (fun x => f x * g x)
    simpa only [e, ← hF, ← hG, ← hFG] using hprod

end PottsContinuity.BD12
