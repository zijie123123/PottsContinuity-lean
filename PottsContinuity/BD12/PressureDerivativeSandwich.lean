module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith

/-! A finite surface error controls derivatives at separated parameters. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Monotone derivatives and a bounded pressure difference yield a derivative
sandwich across every strictly positive parameter gap. -/
theorem pressure_derivative_sandwich (f g f' g' : ℝ → ℝ) (M : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hmf : Monotone f') (hmg : Monotone g')
    (hcost : ∀ x, 0 ≤ g x - f x ∧ g x - f x ≤ M)
    (s t : ℝ) (hst : s < t) :
    f' s ≤ g' t + M / (t-s) := by
  obtain ⟨x,hx,hfx⟩ := exists_hasDerivAt_eq_slope f f' hst
    (fun z _ => (hf z).continuousAt.continuousWithinAt) (fun z _ => hf z)
  obtain ⟨y,hy,hgy⟩ := exists_hasDerivAt_eq_slope g g' hst
    (fun z _ => (hg z).continuousAt.continuousWithinAt) (fun z _ => hg z)
  have hd : 0 < t-s := sub_pos.mpr hst
  have hl : f' s * (t-s) ≤ f t - f s :=
    (le_div_iff₀ hd).mp (hfx ▸ hmf hx.1.le)
  have hu : g t - g s ≤ g' t * (t-s) :=
    (div_le_iff₀ hd).mp (hgy ▸ hmg hy.2.le)
  have hs := (hcost s).2
  have ht := (hcost t).1
  have h : (f' s-g' t)*(t-s) ≤ M := by nlinarith only [hl,hu,hs,ht]
  have h' := (le_div_iff₀ hd).mpr h
  linarith only [h']

end PottsContinuity.BD12
