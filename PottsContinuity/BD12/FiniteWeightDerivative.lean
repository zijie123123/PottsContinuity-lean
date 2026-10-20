module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

/-! Finite product and normalization derivatives used by the corrected DRT formula. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators

/-- Logarithmic derivative of a finite product, without dividing by its factors. -/
theorem hasDerivAt_finset_product_score {E : Type*} (F : Finset E)
    (w : E → ℝ → ℝ) (s : E → ℝ) (x : ℝ)
    (hw : ∀ e ∈ F, HasDerivAt (w e) (w e x * s e) x) :
    HasDerivAt (fun t => ∏ e ∈ F, w e t)
      ((∏ e ∈ F, w e x) * ∑ e ∈ F, s e) x := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty, mul_zero] using hasDerivAt_const x (1 : ℝ)
  | @insert e F he ih =>
    have hF := ih (fun a ha => hw a (Finset.mem_insert_of_mem ha))
    have h := (hw e (Finset.mem_insert_self e F)).mul hF
    simp only [Finset.prod_insert he, Finset.sum_insert he]
    convert h using 1
    ring

/-- Differentiating a finite normalized weighted mean gives its covariance
with the logarithmic weight score. Only the denominator at x must be nonzero. -/
theorem hasDerivAt_normalized_weighted_sum {α : Type*} [Fintype α]
    (w : ℝ → α → ℝ) (s f : α → ℝ) (x : ℝ)
    (hw : ∀ a, HasDerivAt (fun t => w t a) (w x a * s a) x)
    (hZ : (∑ a, w x a) ≠ 0) :
    HasDerivAt (fun t => (∑ a, w t a * f a) / ∑ a, w t a)
      ((∑ a, w x a * (f a * s a)) / (∑ a, w x a) -
        ((∑ a, w x a * f a) / (∑ a, w x a)) *
          ((∑ a, w x a * s a) / (∑ a, w x a))) x := by
  have hN : HasDerivAt (fun t => ∑ a, w t a * f a)
      (∑ a, (w x a * s a) * f a) x :=
    HasDerivAt.fun_sum (fun a _ => (hw a).mul_const (f a))
  have hD : HasDerivAt (fun t => ∑ a, w t a) (∑ a, w x a * s a) x :=
    HasDerivAt.fun_sum (fun a _ => hw a)
  have hsum : (∑ a, (w x a * s a) * f a) = ∑ a, w x a * (f a * s a) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  convert hN.div hD hZ using 1
  rw [hsum]
  field_simp

end PottsContinuity.BD12
