module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

/-- Cross-multiplied conditional lower bounds for two successive events give
the product lower bound for their intersection. The hypotheses are stated
without division, so no positivity-of-conditioning-event convention is
hidden in the lemma. -/
theorem three_event_probability_chain_lower_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B C : Set α) (a b c : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ μ.real A)
    (hAB : b * μ.real A ≤ μ.real (A ∩ B))
    (hABC : c * μ.real (A ∩ B) ≤ μ.real ((A ∩ B) ∩ C)) :
    a * b * c ≤ μ.real (A ∩ B ∩ C) := by
  have hab : a * b ≤ μ.real (A ∩ B) := by
    calc
      a * b ≤ μ.real A * b := mul_le_mul_of_nonneg_right hA hb
      _ = b * μ.real A := by ring
      _ ≤ μ.real (A ∩ B) := hAB
  calc
    a * b * c ≤ μ.real (A ∩ B) * c :=
      mul_le_mul_of_nonneg_right hab hc
    _ = c * μ.real (A ∩ B) := by ring
    _ ≤ μ.real ((A ∩ B) ∩ C) := hABC

end PottsContinuity.Thm4Plane
