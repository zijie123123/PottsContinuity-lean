module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory
noncomputable section

/-- Positive association on measurable upper sets also holds on measurable
lower sets, by taking complements inside a probability space. -/
theorem lowerSet_FKG_of_upperSet_FKG {Ω : Type*} [MeasurableSpace Ω] [Preorder Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAl : IsLowerSet A) (hBl : IsLowerSet B) : μ A * μ B ≤ μ (A ∩ B) := by
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) (hFKG Aᶜ Bᶜ hA.compl hB.compl hAl.compl hBl.compl)
  have hi : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by ext ω; simp
  rw [hi] at hh
  simp only [ENNReal.toReal_mul,← Measure.real_def] at hh
  rw [measureReal_compl hA,measureReal_compl hB,measureReal_compl (hA.union hB)] at hh
  have hone : μ.real Set.univ = 1 := by simp [Measure.real_def]
  rw [hone] at hh
  have hu := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hr : μ.real A * μ.real B ≤ μ.real (A ∩ B) := by nlinarith
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (measure_ne_top μ A) (measure_ne_top μ B))
    (measure_ne_top μ (A ∩ B))).mp
  simpa only [ENNReal.toReal_mul,Measure.real_def] using hr

/-- A measurable order-reversing map transports positive association. -/
theorem upperSet_FKG_map_of_antitone {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Preorder Ω] [Preorder Ξ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (f : Ω → Ξ) (hf : Measurable f) (hanti : Antitone f)
    (A B : Set Ξ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.map f A * μ.map f B ≤ μ.map f (A ∩ B) := by
  rw [Measure.map_apply hf hA,Measure.map_apply hf hB,Measure.map_apply hf (hA.inter hB)]
  apply lowerSet_FKG_of_upperSet_FKG μ hFKG _ _ (hf hA) (hf hB)
  · intro x y hxy hy
    exact hAu (hanti hxy) hy
  · intro x y hxy hy
    exact hBu (hanti hxy) hy

end
end PottsContinuity.PlanarTopology
