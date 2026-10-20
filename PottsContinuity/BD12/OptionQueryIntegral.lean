module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integrate weights attached to the edge returned by a finite optional query.
The no-query output contributes zero, and every edge contributes its own fibre. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- The weighted active-query expectation is the sum of edge weights times
the probabilities of their actual selected-edge fibres. -/
theorem option_query_weight_integral {Ω E : Type*} [MeasurableSpace Ω]
    [Fintype E] [DecidableEq E] [MeasurableSpace (Option E)]
    [MeasurableSingletonClass (Option E)] (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω → Option E) (hq : Measurable q) (a : E → ℝ) :
    let F := fun x => match q x with | none => (0 : ℝ) | some e => a e
    Integrable F μ ∧ (∫ x, F x ∂μ) = ∑ e, a e * μ.real {x | q x = some e} := by
  classical
  let S := fun e => {x | q x = some e}
  have hS (e : E) : MeasurableSet (S e) := (measurableSet_singleton (some e)).preimage hq
  have hi (e : E) : Integrable ((S e).indicator (fun _ : Ω => a e)) μ :=
    (integrable_const (a e)).indicator (hS e)
  have heq : (fun x => match q x with | none => (0 : ℝ) | some e => a e) =
      fun x => ∑ e, (S e).indicator (fun _ : Ω => a e) x := by
    funext x
    cases hx : q x with
    | none => simp [S, hx]
    | some e => simp [S, Set.indicator_apply, hx]
  dsimp only
  rw [heq]
  refine ⟨integrable_finsetSum Finset.univ (fun e _ => hi e), ?_⟩
  rw [integral_finsetSum _ (fun e _ => hi e)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_indicator_const (a e) (hS e), smul_eq_mul, mul_comm]

end PottsContinuity.BD12
