module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-! The probability part of KST's cascading and closing relations.
The geometric hypotheses are event inclusions, not probability estimates. -/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] [Preorder Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Positive association improves the union bound for two increasing events. -/
theorem kst_union_bound
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.real (A ∪ B) ≤ 1 - (1 - μ.real A) * (1 - μ.real B) := by
  have hf := hFKG A B hA hB hAu hBu
  have hu := measureReal_union_add_inter (μ := μ) (s := A) hB
  nlinarith

/-- The two-event square-root trick, including both probability endpoints. -/
theorem kst_square_root_trick
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ max (μ.real A) (μ.real B) := by
  have hu := kst_union_bound μ hFKG hA hB hAu hBu
  have ha : μ.real A ≤ 1 := measureReal_le_one
  have hb : μ.real B ≤ 1 := measureReal_le_one
  have hu1 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  have hs := Real.sq_sqrt (sub_nonneg.mpr hu1)
  have hs0 := Real.sqrt_nonneg (1 - μ.real (A ∪ B))
  rcases le_total (μ.real A) (μ.real B) with hab | hba
  · rw [max_eq_right hab]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hab)]
  · rw [max_eq_left hba]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hba)]

/-- KST's cascade from precisely the two geometric inclusions. Translation
invariance identifies the probabilities of the two translated bridge events.
This is conditional on corridor geometry, not a proof of that geometry. -/
theorem kst_cascade_of_kstCorridor
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {Qbig Qsmall E Qmid Bleft Bright : Set Ω}
    (hQs : MeasurableSet Qsmall) (hE : MeasurableSet E)
    (hQm : MeasurableSet Qmid) (hBl : MeasurableSet Bleft)
    (hBr : MeasurableSet Bright)
    (hQsu : IsUpperSet Qsmall) (hEu : IsUpperSet E)
    (hQmu : IsUpperSet Qmid) (hBlu : IsUpperSet Bleft)
    (hBru : IsUpperSet Bright)
    (hpartition : Qbig ⊆ Qsmall ∪ E)
    (hcorridor : E ∩ Qmid ⊆ Bleft ∪ Bright)
    (hsym : μ.real Bright = μ.real Bleft) (hq : 0 < μ.real Qmid) :
    1 - Real.sqrt (1 - μ.real Qbig) ≤
      max (μ.real Qsmall)
        ((1 - (1 - μ.real Bleft) ^ 2) / μ.real Qmid) := by
  have heq := hFKG E Qmid hE hQm hEu hQmu
  have hcover := measureReal_mono (μ := μ) hcorridor
  have hbridge := kst_union_bound μ hFKG hBl hBr hBlu hBru
  rw [hsym] at hbridge
  have he : μ.real E ≤ (1 - (1 - μ.real Bleft) ^ 2) / μ.real Qmid := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hroot := kst_square_root_trick μ hFKG hQs hE hQsu hEu
  have hpart := measureReal_mono (μ := μ) hpartition
  have hsqrt := Real.sqrt_le_sqrt (sub_le_sub_left hpart 1)
  exact (sub_le_sub_left hsqrt 1).trans
    (hroot.trans (max_le_max le_rfl he))

/-- Closing uses only FKG and the deterministic bridge inclusion. -/
theorem kst_closing_of_kstCorridor
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {Q Bsmall Bbig : Set Ω} (hQ : MeasurableSet Q)
    (hB : MeasurableSet Bsmall) (hQu : IsUpperSet Q) (hBu : IsUpperSet Bsmall)
    (hclosing : Q ∩ Bsmall ⊆ Bbig) :
    μ.real Q * μ.real Bsmall ≤ μ.real Bbig :=
  (hFKG Q Bsmall hQ hB hQu hBu).trans (measureReal_mono hclosing)

end PottsContinuity.BD12
