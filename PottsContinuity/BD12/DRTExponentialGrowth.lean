module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-! The integrating-factor step of DRT's scalar sharpness bootstrap. Honest
pointwise derivative bounds imply an exponential bound between two parameters. -/

@[expose] public section

namespace PottsContinuity.BD12
open Set

/-- Integrate f'>=c*f on an interval, with continuity at its endpoints and
actual derivatives on its interior. The coefficient c can be any real number. -/
theorem drt_exponential_bound_of_derivative_growth
    (f f' : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgrowth : ∀ x ∈ Ioo a b, c * f x ≤ f' x) :
    f a ≤ f b * Real.exp (-c * (b - a)) := by
  let g := fun x => Real.exp (-c * x) * f x
  have hgcont : ContinuousOn g (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf
  have hgderiv (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt g (Real.exp (-c * x) * (f' x - c * f x)) x := by
    have h := (((hasDerivAt_id x).const_mul (-c)).exp).mul (hderiv x hx)
    convert h using 1
    all_goals first | (funext y; rfl) | (dsimp only [g, id_eq, Pi.mul_apply]; ring)
  have hgmono : MonotoneOn g (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hgcont
    · intro x hx
      exact (hgderiv x (by simpa only [interior_Icc] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      rw [(hgderiv x hx').deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hgrowth x hx'))
  have hend := hgmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  change Real.exp (-c * a) * f a ≤ Real.exp (-c * b) * f b at hend
  calc
    f a = Real.exp (c * a) * (Real.exp (-c * a) * f a) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (c * a) * (Real.exp (-c * b) * f b) :=
      mul_le_mul_of_nonneg_left hend (Real.exp_pos _).le
    _ = f b * Real.exp (-c * (b - a)) := by
      rw [← mul_assoc, ← Real.exp_add, show c * a + -c * b = -c * (b - a) by ring]
      exact mul_comm _ _

end PottsContinuity.BD12
