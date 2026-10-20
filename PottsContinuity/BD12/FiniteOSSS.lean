module

public import PottsContinuity.BD12.FiniteOSSSQuerySum
public import PottsContinuity.BD12.ActiveQueryRevealment
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Finite monotone-measure OSSS for an actual stopping reveal tree and its
usual revealment probability. All expectations and revealments are constructed
from the independent original uniforms, with no probabilistic premises hidden. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Probability that the actual original exploration queries e before the
observable is determined, under its complete independent uniform input law. -/
def finiteRevealment (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U : ℕ → ℝ) (T : FiniteRevealTree E ∅) (e : E) : ℝ :=
  (finiteOriginalPinBlock 0 (Fintype.card E) U).real
    {W | ∃ t ∈ Finset.range (Fintype.card E), finiteActiveOriginalQueryAt w f W t T ∅ = some e}

/-- OSSS for positive finite lattice weights and a monotone unit observable,
with the usual probability of revealing each edge in its actual algorithm. -/
theorem finite_osss_monotone
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]
    [MeasurableSpace (Option E)] [MeasurableSingletonClass (Option E)]
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    finitePinnedMean w ∅ ∅ (fun A => f A ^ 2) - (finitePinnedMean w ∅ ∅ f) ^ 2 ≤
      ∑ e, finiteRevealment w f U T e *
        (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
          finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0)) := by
  have h := finite_osss_query_sum w hw f hf hf01 U V T
  simp_rw [finiteActiveOriginalQueryAt_sum_eq_revealment] at h
  exact h

end
end PottsContinuity.BD12
