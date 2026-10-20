-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteConditionalEventBounds.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RevealRecordEventDisintegration
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace PottsContinuity.FKC.FiniteFK

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance conditionalEventRangeFintype (r : α → β) : Fintype (Set.range r) := Fintype.ofFinite _
local instance conditionalEventMeasurableSpace : MeasurableSpace α := ⊤
local instance conditionalEventMeasurableSingleton : MeasurableSingletonClass α :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

omit [Fintype α] [Nonempty α] in
 theorem statistic_fiber_support (p : PMF α) (hp : ∀ a, p a ≠ 0)
    (r : α → β) (y : Set.range r) :
    ∃ a ∈ {a | r a = y.1}, a ∈ p.support := by
  obtain ⟨a, ha⟩ := y.2
  exact ⟨a, ha, (p.mem_support_iff a).2 (hp a)⟩

/-- The true normalized restriction of a full-support finite PMF to one attained
fiber of a statistic. -/
noncomputable def finiteStatisticConditionalPMF
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (y : Set.range r) : PMF α :=
  p.filter {a | r a = y.1} (statistic_fiber_support p hp r y)

def statisticFiberMeets (r : α → β) (S : Set α) (y : Set.range r) : Prop :=
  ∃ a, r a = y.1 ∧ a ∈ S

local instance statisticFiberMeetsDecidable (r : α → β) (S : Set α) (y : Set.range r) :
    Decidable (statisticFiberMeets r S y) := Classical.propDecidable _

omit [Nonempty α] in
private theorem finiteStatistic_sum_formula
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (E : Set α) :
    (p.toMeasure E).toReal =
      ∑ y : Set.range r,
        ((p.map (Set.rangeFactorization r)) y).toReal *
          ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal := by
  simpa [finiteStatisticConditionalPMF] using
    (pmf_toMeasure_event_toReal_eq_sum p hp r E)

omit [Nonempty α] in
private theorem statistic_conditional_inter
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (S E : Set α)
    (hS : ∀ a b, r a = r b → (a ∈ S ↔ b ∈ S)) (y : Set.range r) :
    ((finiteStatisticConditionalPMF p hp r y).toMeasure (S ∩ E)).toReal =
      if statisticFiberMeets r S y then
        ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal else 0 := by
  classical
  let c := finiteStatisticConditionalPMF p hp r y
  by_cases hy : statisticFiberMeets r S y
  · have hy' : statisticFiberMeets r S y := hy
    obtain ⟨a₀, ha₀, ha₀S⟩ := hy
    have hsupp : c.support ⊆ S := by
      intro a ha
      have hfa : r a = y.1 :=
        (PMF.mem_support_filter_iff (h := statistic_fiber_support p hp r y)).mp ha |>.1
      exact (hS a a₀ (hfa.trans ha₀.symm)).mpr ha₀S
    have hsets : (S ∩ E) ∩ c.support = E ∩ c.support := by
      ext a
      constructor
      · rintro ⟨⟨_, he⟩, ha⟩
        exact ⟨he, ha⟩
      · rintro ⟨he, ha⟩
        exact ⟨⟨hsupp ha, he⟩, ha⟩
    have heq := c.toMeasure_apply_eq_of_inter_support_eq
      (MeasurableSet.of_discrete (s := S ∩ E)) (MeasurableSet.of_discrete (s := E)) hsets
    have hreal := congrArg ENNReal.toReal heq
    simpa [hy', c] using hreal
  · have hsets : (S ∩ E) ∩ c.support = (∅ : Set α) ∩ c.support := by
      ext a
      constructor
      · rintro ⟨⟨haS, _⟩, ha⟩
        have hfa : r a = y.1 :=
          (PMF.mem_support_filter_iff (h := statistic_fiber_support p hp r y)).mp ha |>.1
        have hnot : ¬ a ∈ S := by
          intro has
          exact hy ⟨a, hfa, has⟩
        exact (hnot haS).elim
      · simp
    have heq := c.toMeasure_apply_eq_of_inter_support_eq
      (MeasurableSet.of_discrete (s := S ∩ E))
      (MeasurableSet.of_discrete (s := (∅ : Set α))) hsets
    have hreal := congrArg ENNReal.toReal heq
    simpa [hy, c] using hreal

omit [Nonempty α] in
private theorem statistic_conditional_selector
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (S : Set α)
    (hS : ∀ a b, r a = r b → (a ∈ S ↔ b ∈ S)) (y : Set.range r) :
    ((finiteStatisticConditionalPMF p hp r y).toMeasure S).toReal =
      if statisticFiberMeets r S y then 1 else 0 := by
  have h := statistic_conditional_inter p hp r S Set.univ hS y
  simpa [Set.inter_univ] using h

omit [Nonempty α] in
theorem finiteConditional_event_lower_bound
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β)
    (S E : Set α) (c : ℝ)
    (hS : ∀ a b, r a = r b → (a ∈ S ↔ b ∈ S))
    (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1)
    (hcond : ∀ y : Set.range r,
      c ≤ ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal) :
    c * (p.toMeasure S).toReal ≤ (p.toMeasure (S ∩ E)).toReal := by
  classical
  let m (y : Set.range r) := ((p.map (Set.rangeFactorization r)) y).toReal
  let sprob (y : Set.range r) := ((finiteStatisticConditionalPMF p hp r y).toMeasure S).toReal
  let joint (y : Set.range r) :=
    ((finiteStatisticConditionalPMF p hp r y).toMeasure (S ∩ E)).toReal
  have hterm (y : Set.range r) : c * (m y * sprob y) ≤ m y * joint y := by
    by_cases hy : statisticFiberMeets r S y
    · have hs := statistic_conditional_selector p hp r S hS y
      have hj := statistic_conditional_inter p hp r S E hS y
      dsimp [sprob, joint]
      rw [hs, hj]
      simp only [ite_eq_left hy]
      have hm : 0 ≤ m y := ENNReal.toReal_nonneg
      nlinarith [hcond y]
    · have hs := statistic_conditional_selector p hp r S hS y
      have hj := statistic_conditional_inter p hp r S E hS y
      dsimp [sprob, joint]
      rw [hs, hj]
      simp only [ite_eq_right hy]
      simp
  rw [finiteStatistic_sum_formula p hp r S,
    finiteStatistic_sum_formula p hp r (S ∩ E)]
  calc
    c * ∑ y : Set.range r, m y * sprob y =
        ∑ y : Set.range r, c * (m y * sprob y) := by rw [Finset.mul_sum]
    _ ≤ ∑ y : Set.range r, m y * joint y := Finset.sum_le_sum fun y hy => hterm y
    _ = ∑ y : Set.range r,
        ((p.map (Set.rangeFactorization r)) y).toReal *
          ((finiteStatisticConditionalPMF p hp r y).toMeasure (S ∩ E)).toReal := by
        apply Finset.sum_congr rfl
        intro y hy
        rfl

omit [Nonempty α] in
theorem finiteConditional_event_complement_upper_bound
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β)
    (S E : Set α) (c : ℝ)
    (hS : ∀ a b, r a = r b → (a ∈ S ↔ b ∈ S))
    (_hc0 : 0 ≤ c) (_hc1 : c ≤ 1)
    (hcond : ∀ y : Set.range r,
      c ≤ ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal) :
    (p.toMeasure (S \ E)).toReal ≤ (1-c) * (p.toMeasure S).toReal := by
  classical
  let m (y : Set.range r) := ((p.map (Set.rangeFactorization r)) y).toReal
  let sprob (y : Set.range r) :=
    ((finiteStatisticConditionalPMF p hp r y).toMeasure S).toReal
  let bad (y : Set.range r) :=
    ((finiteStatisticConditionalPMF p hp r y).toMeasure (S \ E)).toReal
  have hcondBad (y : Set.range r) :
      ((finiteStatisticConditionalPMF p hp r y).toMeasure Eᶜ).toReal ≤ 1-c := by
    let μ := (finiteStatisticConditionalPMF p hp r y).toMeasure
    have hprob : (μ E).toReal + (μ Eᶜ).toReal = 1 := by
      simpa [μ, Measure.real] using
        (MeasureTheory.probReal_add_probReal_compl (μ := μ) (s := E)
          (MeasurableSet.of_discrete (s := E)))
    linarith [hprob, hcond y]
  have hterm (y : Set.range r) :
      m y * bad y ≤ (1-c) * (m y * sprob y) := by
    by_cases hy : statisticFiberMeets r S y
    · have hs := statistic_conditional_selector p hp r S hS y
      have hj := statistic_conditional_inter p hp r S Eᶜ hS y
      dsimp [sprob, bad]
      rw [Set.sdiff_eq, hs, hj]
      simp only [ite_eq_left hy]
      have hm : 0 ≤ m y := ENNReal.toReal_nonneg
      have hm' := mul_le_mul_of_nonneg_left (hcondBad y) hm
      nlinarith [hm']
    · have hs := statistic_conditional_selector p hp r S hS y
      have hj := statistic_conditional_inter p hp r S Eᶜ hS y
      dsimp [sprob, bad]
      rw [Set.sdiff_eq, hs, hj]
      simp only [ite_eq_right hy]
      simp
  rw [finiteStatistic_sum_formula p hp r (S \ E)]
  calc
    ∑ y : Set.range r, m y * bad y ≤
        ∑ y : Set.range r, (1-c) * (m y * sprob y) :=
          Finset.sum_le_sum fun y hy => hterm y
    _ = (1-c) * ∑ y : Set.range r, m y * sprob y := by rw [Finset.mul_sum]
    _ = (1-c) * (p.toMeasure S).toReal := by
      rw [finiteStatistic_sum_formula p hp r S]

end PottsContinuity.FKC.FiniteFK
