-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteConditionalGoodFiberBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteConditionalEventBounds

@[expose] public section

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace PottsContinuity.FKC.FiniteFK

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance goodFiberRangeFintype (r : α → β) : Fintype (Set.range r) :=
  Fintype.ofFinite _
local instance goodFiberMeasurableSpace : MeasurableSpace α := ⊤
local instance goodFiberMeasurableSingleton : MeasurableSingletonClass α :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

omit [Nonempty α] in
/-- The finite conditional lower bound only needs to hold on attained records
whose fiber meets the stable good event. A bad record contributes no mass to
that event, so its conditional probability of `E ∪ Sᶜ` is one. -/
theorem finiteConditional_event_lower_bound_on_good_fibers
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β)
    (S E : Set α) (c : ℝ)
    (hS : ∀ a b, r a = r b → (a ∈ S ↔ b ∈ S))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcond : ∀ y : Set.range r,
      (∃ a, r a = y.1 ∧ a ∈ S) →
        c ≤ ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal) :
    c * (p.toMeasure S).toReal ≤ (p.toMeasure (S ∩ E)).toReal := by
  classical
  have hcond' : ∀ y : Set.range r,
      c ≤ ((finiteStatisticConditionalPMF p hp r y).toMeasure (E ∪ Sᶜ)).toReal := by
    intro y
    by_cases hy : ∃ a, r a = y.1 ∧ a ∈ S
    · have hc := hcond y hy
      have hmono :
          ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal ≤
            ((finiteStatisticConditionalPMF p hp r y).toMeasure (E ∪ Sᶜ)).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono (fun _ ha => Or.inl ha))
      exact hc.trans hmono
    · let μ := finiteStatisticConditionalPMF p hp r y
      have hsupport : μ.support ⊆ Sᶜ := by
        intro a ha
        have hfilter : a ∈ {a : α | r a = y.1} ∧ a ∈ p.support := by
          simpa [μ, finiteStatisticConditionalPMF, PMF.mem_support_filter_iff] using ha
        change a ∉ S
        intro haS
        exact hy ⟨a, hfilter.1, haS⟩
      have hμ : μ.toMeasure (E ∪ Sᶜ) = 1 := by
        rw [μ.toMeasure_apply_eq_one_iff (MeasurableSet.of_discrete
          (s := E ∪ Sᶜ))]
        intro a ha
        exact Or.inr (hsupport ha)
      rw [hμ]
      exact hc1
  simpa [Set.inter_union_distrib_left] using
    (finiteConditional_event_lower_bound p hp r S (E ∪ Sᶜ) c
      hS hc0 hc1 hcond')

end PottsContinuity.FKC.FiniteFK

