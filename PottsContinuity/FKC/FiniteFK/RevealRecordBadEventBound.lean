-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RevealRecordBadEventBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RevealRecordEventDisintegration
public import PottsContinuity.FKC.FiniteFK.Expectation
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance revealRecordBadEventDomainMeasurableSpace : MeasurableSpace α := ⊤
local instance revealRecordBadEventDomainDiscrete : DiscreteMeasurableSpace α :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

local instance revealRecordBadEventRangeFintype (r : α → β) :
    Fintype (Set.range r) := Fintype.ofFinite _
local instance revealRecordBadEventRangeMeasurableSpace (r : α → β) :
    MeasurableSpace (Set.range r) := ⊤
local instance revealRecordBadEventRangeDiscrete (r : α → β) :
    DiscreteMeasurableSpace (Set.range r) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

omit [Fintype α] [Nonempty α] in
 theorem revealRecordBadEvent_fiberSupport
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (y : Set.range r) :
    ∃ a ∈ {a | r a = y.1}, a ∈ p.support := by
  obtain ⟨a, ha⟩ := y.2
  exact ⟨a, ha, (p.mem_support_iff a).2 (hp a)⟩

def revealRecordBadEventConditional
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β)
    (y : Set.range r) : PMF α :=
  p.filter {a | r a = y.1} (revealRecordBadEvent_fiberSupport p hp r y)

omit [Nonempty α] in
/-- Conditional averaging over actual attained records: good records have
conditional event probability at most `c`; bad records are charged only their
actual marginal mass. No independence or equal-record-weight assumption is
used. -/
theorem pmf_event_probability_le_good_record_bound_add_bad_mass
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β)
    (B : Set (Set.range r)) (E : Set α) (c : ℝ) (hc : 0 ≤ c)
    (hgood : ∀ y : Set.range r, y ∉ B →
      (((p.filter {a | r a = y.1}
        (revealRecordBadEvent_fiberSupport p hp r y)).toMeasure E).toReal ≤ c)) :
    (p.toMeasure E).toReal ≤
      c + ((p.map (Set.rangeFactorization r)).toMeasure B).toReal := by
  classical
  let ν : PMF (Set.range r) := p.map (Set.rangeFactorization r)
  let Q : Set.range r → PMF α := revealRecordBadEventConditional p hp r
  have hdecomp : (p.toMeasure E).toReal =
      ∑ y : Set.range r, (ν y).toReal * (((Q y).toMeasure E).toReal) := by
    simpa [ν, Q, revealRecordBadEventConditional,
      revealRecordBadEvent_fiberSupport] using
      (pmf_toMeasure_event_toReal_eq_sum p hp r E)
  have hmass : ∑ y : Set.range r, (ν y).toReal = 1 :=
    FiniteProbability.sum_mass_toReal ν
  have hbad :
      ∑ y : Set.range r, (if y ∈ B then (ν y).toReal else 0) =
        (ν.toMeasure B).toReal := by
    rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro y hy
      by_cases hyB : y ∈ B <;> simp [Set.indicator, hyB]
    · intro y hy
      by_cases hyB : y ∈ B
      · simpa [Set.indicator, hyB] using ν.apply_ne_top y
      · simp [Set.indicator, hyB]
  have hcond_le_one (y : Set.range r) : ((Q y).toMeasure E).toReal ≤ 1 := by
    have : IsProbabilityMeasure (Q y).toMeasure := PMF.toMeasure.isProbabilityMeasure _
    have hmeasure : (Q y).toMeasure E ≤ 1 := by
      calc
        (Q y).toMeasure E ≤ (Q y).toMeasure Set.univ := measure_mono (Set.subset_univ E)
        _ = 1 := measure_univ
    calc
      ((Q y).toMeasure E).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top hmeasure
      _ = 1 := ENNReal.toReal_one
  have hterm (y : Set.range r) :
      (ν y).toReal * ((Q y).toMeasure E).toReal ≤
        c * (ν y).toReal + (if y ∈ B then (ν y).toReal else 0) := by
    by_cases hyB : y ∈ B
    · have hν : 0 ≤ (ν y).toReal := ENNReal.toReal_nonneg
      have hcond := hcond_le_one y
      simp only [ite_eq_left hyB]
      nlinarith [mul_nonneg hc (ν y).toReal_nonneg]
    · have hgood_y := hgood y hyB
      have hν : 0 ≤ (ν y).toReal := ENNReal.toReal_nonneg
      have hmul := mul_le_mul_of_nonneg_left hgood_y hν
      simpa [Q, revealRecordBadEventConditional, hyB, mul_comm] using hmul
  calc
    (p.toMeasure E).toReal =
        ∑ y : Set.range r, (ν y).toReal * ((Q y).toMeasure E).toReal := hdecomp
    _ ≤ ∑ y : Set.range r,
        (c * (ν y).toReal + (if y ∈ B then (ν y).toReal else 0)) :=
      Finset.sum_le_sum (fun y _ => hterm y)
    _ = c + (ν.toMeasure B).toReal := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmass, mul_one, hbad]
    _ = c + ((p.map (Set.rangeFactorization r)).toMeasure B).toReal := by rfl

end
end PottsContinuity.FKC.FiniteFK
