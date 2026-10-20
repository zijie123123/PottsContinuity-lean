-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedConditionalEvent.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedReveal
public import PottsContinuity.FKC.FiniteFK.FiniteConditionalEventBounds
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction
public import PottsContinuity.FKC.FiniteFK.Expectation
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory FiniteProbability

noncomputable section

local instance pairedConditionalEdgeFintype (n : ℕ) :
    Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
local instance pairedConditionalEdgeDecidableEq (n : ℕ) :
    DecidableEq (slitBoxGraph n).edgeSet := Classical.decEq _
local instance pairedConditionalConfigFintype (n : ℕ) :
    Fintype (Configuration (slitBoxGraph n)) := Fintype.ofFinite _
local instance pairedConditionalConfigNonempty (n : ℕ) :
    Nonempty (Configuration (slitBoxGraph n)) := ⟨∅⟩
local instance pairedConditionalConfigMeasurable (n : ℕ) :
    MeasurableSpace (Configuration (slitBoxGraph n)) := ⊤
local instance pairedConditionalConfigDiscrete (n : ℕ) :
    DiscreteMeasurableSpace (Configuration (slitBoxGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

private theorem paired_pmf_expectation_indicator_eq_toMeasure
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (E : Set α) :
    expectation p (E.indicator (fun _ => (1 : ℝ))) = (p.toMeasure E).toReal := by
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x ∈ E <;> simp [Set.indicator, h]
  · intro x hx
    by_cases h : x ∈ E <;> simp [Set.indicator, h, p.apply_ne_top]

/-- At an attained paired reveal record, every full-configuration event has
exactly the probability of that event after restoring the record's frozen
open edges to the genuine remaining-law sample. -/
theorem slitBoxPairedConditional_event_toReal_eq_remaining_restoration
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (q : ClusterWeight) (A : Configuration (slitBoxGraph n))
    (E : Set (Configuration (slitBoxGraph n))) :
    ((finiteStatisticConditionalPMF (law (slitBoxGraph n) q (slitBoxBoundary n))
      (fun C => (law_pos (slitBoxGraph n) q (slitBoxBoundary n) C).ne')
      (revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ))
      ⟨revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) A,
        ⟨A, rfl⟩⟩).toMeasure E).toReal =
      ((remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n)
          (A ∩ slitBoxPairedReveal n hn u huY huX δ A))
        (slitBoxPairedReveal n hn u huY huX δ A)).toMeasure
        ({B | B.val ∪ (A ∩ slitBoxPairedReveal n hn u huY huX δ A) ∈ E})).toReal := by
  classical
  let R := slitBoxPairedReveal n hn u huY huX δ A
  let H : RemovedConfiguration (slitBoxGraph n) R :=
    ⟨A ∩ R, Finset.inter_subset_right⟩
  let r := revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ)
  let y : Set.range r := ⟨r A, ⟨A, rfl⟩⟩
  let μ := finiteStatisticConditionalPMF
    (law (slitBoxGraph n) q (slitBoxBoundary n))
    (fun C => (law_pos (slitBoxGraph n) q (slitBoxBoundary n) C).ne') r y
  let split := fun C : Configuration (slitBoxGraph n) =>
    (configurationSplitEquiv (slitBoxGraph n) R C).1
  let restoredEvent : Set (RemainingConfiguration (slitBoxGraph n) R) :=
    {B | B.val ∪ H.val ∈ E}
  have hrecord : {C : Configuration (slitBoxGraph n) | r C = r A} =
      revealRecordEvent (slitBoxGraph n) (slitBoxPairedReveal n hn u huY huX δ) A := by
    change {C : Configuration (slitBoxGraph n) |
      revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) C =
        revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) A} = _
    exact revealRecordStatistic_fiber_eq _ _
  have hfilter : μ = ((law (slitBoxGraph n) q (slitBoxBoundary n)).filter
      (revealRecordEvent (slitBoxGraph n)
        (slitBoxPairedReveal n hn u huY huX δ) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent (slitBoxGraph n)
          (slitBoxPairedReveal n hn u huY huX δ)
          (slitBoxPairedReveal_stopping_consistency n hn u huY huX δ) A]
        exact frozenStateEvent_support q (slitBoxBoundary n) R H)) := by
    dsimp [μ, finiteStatisticConditionalPMF, y]
    apply PMF.ext
    intro C
    simp only [PMF.filter_apply]
    rw [hrecord]
  have hmap : μ.map split = remainingLaw (slitBoxGraph n) q
      (frozenBoundary (slitBoxBoundary n) H.val) R := by
    have hm := slitBoxPairedReveal_law_filter_map_remaining n hn u huY huX δ q A
    rw [hfilter]
    simpa [split, R, H, revealRecordConfiguration] using hm
  have hsupp : ∀ C, C ∈ μ.support → C ∈ revealRecordEvent
      (slitBoxGraph n) (slitBoxPairedReveal n hn u huY huX δ) A := by
    intro C hC
    have hfiber : r C = y.1 := by
      have hfilter : C ∈ {C : Configuration (slitBoxGraph n) | r C = y.1} ∧
          C ∈ (law (slitBoxGraph n) q (slitBoxBoundary n)).support := by
        simpa [μ, finiteStatisticConditionalPMF, PMF.mem_support_filter_iff] using hC
      exact hfilter.1
    have hfiber' : r C = r A := by simpa [y] using hfiber
    have hmem : C ∈ {C : Configuration (slitBoxGraph n) | r C = r A} := hfiber'
    have hpred : (r C = r A) ↔ C ∈ revealRecordEvent
        (slitBoxGraph n) (slitBoxPairedReveal n hn u huY huX δ) A := by
      exact Set.ext_iff.mp hrecord C
    exact hpred.mp hfiber'
  have hrestore (C : Configuration (slitBoxGraph n))
      (hC : C ∈ revealRecordEvent
        (slitBoxGraph n) (slitBoxPairedReveal n hn u huY huX δ) A) :
      C = (split C).val ∪ H.val := by
    have hremoved : (configurationSplitEquiv (slitBoxGraph n) R C).2 = H := by
      apply Subtype.ext
      change C ∩ R = A ∩ R
      exact hC.2
    have hs := (configurationSplitEquiv (slitBoxGraph n) R).symm_apply_apply C
    change (split C).val ∪ (configurationSplitEquiv (slitBoxGraph n) R C).2.val = C at hs
    rw [hremoved] at hs
    exact hs.symm
  have hterms (C : Configuration (slitBoxGraph n)) :
      (μ C).toReal * E.indicator (fun _ => (1 : ℝ)) C =
        (μ C).toReal * restoredEvent.indicator (fun _ => (1 : ℝ)) (split C) := by
    by_cases hμ : μ C = 0
    · simp [hμ]
    · have hC : C ∈ μ.support := (μ.mem_support_iff C).2 hμ
      have hrec := hsupp C hC
      have hevent : C ∈ E ↔ split C ∈ restoredEvent := by
        change C ∈ E ↔ (split C).val ∪ H.val ∈ E
        rw [← hrestore C hrec]
      simp [Set.indicator, hevent]
  have hexpect : expectation μ (E.indicator (fun _ => (1 : ℝ))) =
      expectation (μ.map split) (restoredEvent.indicator (fun _ => (1 : ℝ))) := by
    rw [expectation_map]
    unfold expectation
    apply Finset.sum_congr rfl
    intro C hC
    exact hterms C
  have hmeasureLeft := paired_pmf_expectation_indicator_eq_toMeasure μ E
  have hmeasureRight := paired_pmf_expectation_indicator_eq_toMeasure
    (μ.map split) restoredEvent
  have hmeasureRemaining := paired_pmf_expectation_indicator_eq_toMeasure
    (remainingLaw (slitBoxGraph n) q
      (frozenBoundary (slitBoxBoundary n) H.val) R) restoredEvent
  calc
    ((μ.toMeasure E).toReal) = expectation μ (E.indicator (fun _ => (1 : ℝ))) :=
      hmeasureLeft.symm
    _ = expectation (μ.map split) (restoredEvent.indicator (fun _ => (1 : ℝ))) := hexpect
    _ = expectation (remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n) H.val) R)
        (restoredEvent.indicator (fun _ => (1 : ℝ))) := by rw [hmap]
    _ = ((remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n)
          (A ∩ slitBoxPairedReveal n hn u huY huX δ A))
        (slitBoxPairedReveal n hn u huY huX δ A)).toMeasure
        {B | B.val ∪ (A ∩ slitBoxPairedReveal n hn u huY huX δ A) ∈ E}).toReal := by
      simpa [R, H, restoredEvent] using hmeasureRemaining

end

end PottsContinuity.FKC.FiniteFK

