module

public import PottsContinuity.FKC.FiniteFK.FiniteConditionalGoodFiberBound

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Exploration

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance finiteFiberComparisonMeasurableSpace : MeasurableSpace α := ⊤
local instance finiteFiberComparisonMeasurableSingleton : MeasurableSingletonClass α :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

omit [Nonempty α] in
/-- A finite selector whose good event is invariant on selector fibres obeys
an event comparison with an additive bad-event error whenever every good
fibre has conditional probability at most the reference value. -/
theorem pmf_event_le_reference_add_bad_of_goodFiberBound
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (record : α → β)
    (good event : Set α) (reference : ℝ)
    (hgoodStable : ∀ a b, record a = record b → (a ∈ good ↔ b ∈ good))
    (hreference_nonneg : 0 ≤ reference) (hreference_le_one : reference ≤ 1)
    (hfiber : ∀ y : Set.range record,
      (∃ a, record a = y.1 ∧ a ∈ good) →
        ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
          p hp record y).toMeasure event).toReal ≤ reference) :
    (p.toMeasure event).toReal ≤
      reference + (p.toMeasure goodᶜ).toReal := by
  classical
  have hconditional_complement (y : Set.range record)
      (hy : ∃ a, record a = y.1 ∧ a ∈ good) :
      1 - reference ≤
        ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
          p hp record y).toMeasure eventᶜ).toReal := by
    let ν := (PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      p hp record y).toMeasure
    have hsum : (ν event).toReal + (ν eventᶜ).toReal = 1 := by
      simpa [ν, Measure.real] using
        (MeasureTheory.probReal_add_probReal_compl
          (μ := ν) (s := event) (MeasurableSet.of_discrete (s := event)))
    linarith [hfiber y hy]
  have hgood_complement :=
    PottsContinuity.FKC.FiniteFK.finiteConditional_event_lower_bound_on_good_fibers
      p hp record good eventᶜ (1 - reference) hgoodStable
      (by linarith) (by linarith) hconditional_complement
  let μ := p.toMeasure
  let : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure p
  have hgood_decomp :
      μ.real (good ∩ eventᶜ) + μ.real (good \ (good ∩ eventᶜ)) = μ.real good := by
    have h := MeasureTheory.measureReal_add_sdiff
      (μ := μ) (s := good ∩ eventᶜ) (t := good)
      (MeasurableSet.of_discrete (s := good ∩ eventᶜ))
    rw [Set.union_eq_right.mpr Set.inter_subset_left] at h
    exact h
  have hgood_part :
      μ.real (good ∩ event) ≤ reference * μ.real good := by
    have hset : good \ (good ∩ eventᶜ) = good ∩ event := by
      ext a
      simp [Set.mem_inter_iff]
    rw [hset] at hgood_decomp
    have hcomp_nonneg : 0 ≤ μ.real (good ∩ eventᶜ) := ENNReal.toReal_nonneg
    have hprob_nonneg : 0 ≤ μ.real good := ENNReal.toReal_nonneg
    have hgood_complement' :
        (1 - reference) * μ.real good ≤ μ.real (good ∩ eventᶜ) := by
      simpa [μ, Measure.real] using hgood_complement
    nlinarith [hgood_decomp, hgood_complement']
  have herror_subset : event \ (good ∩ event) ⊆ goodᶜ := by
    intro a ha hgood
    exact ha.2 ⟨hgood, ha.1⟩
  have hgood_compl_finite : μ (goodᶜ) ≠ ⊤ := by
    have hlt : μ (goodᶜ) < ⊤ := by
      calc
        μ (goodᶜ) ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ < ⊤ := ENNReal.one_lt_top
    exact ne_of_lt hlt
  have herror := MeasureTheory.measureReal_mono herror_subset hgood_compl_finite
  have hgood_prob : μ.real good ≤ 1 := by
    calc
      μ.real good ≤ μ.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp [μ, Measure.real]
  have hdecomp :
      μ.real (good ∩ event) + μ.real (event \ (good ∩ event)) = μ.real event := by
    have h := MeasureTheory.measureReal_add_sdiff
      (μ := μ) (s := good ∩ event) (t := event)
      (MeasurableSet.of_discrete (s := good ∩ event))
    rw [Set.union_eq_right.mpr Set.inter_subset_right] at h
    exact h
  have hfinal :
      μ.real event ≤ reference + μ.real goodᶜ := by
    calc
      μ.real event = μ.real (good ∩ event) + μ.real (event \ (good ∩ event)) := hdecomp.symm
      _ ≤ reference * μ.real good + μ.real goodᶜ := add_le_add hgood_part herror
      _ ≤ reference + μ.real goodᶜ := by
        exact add_le_add
          (by
            calc
              reference * μ.real good ≤ reference * 1 :=
                mul_le_mul_of_nonneg_left hgood_prob hreference_nonneg
              _ = reference := by ring)
          le_rfl
  simpa [μ, Measure.real] using hfinal

end PottsContinuity.Exploration
