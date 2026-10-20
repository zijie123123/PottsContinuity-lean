-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RevealRecordEventDisintegration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RevealRecordDisintegration

@[expose] public section

open scoped BigOperators
open MeasureTheory
noncomputable section

namespace PottsContinuity.FKC.FiniteFK

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance eventRangeFintype (r : α → β) : Fintype (Set.range r) := Fintype.ofFinite _

omit [Fintype α] [Nonempty α] in
 theorem event_fiber_support (p : PMF α) (hp : ∀ a, p a ≠ 0)
    (r : α → β) (y : Set.range r) :
    ∃ a ∈ {a | r a = y.1}, a ∈ p.support := by
  obtain ⟨a, ha⟩ := y.2
  exact ⟨a, ha, (p.mem_support_iff a).2 (hp a)⟩

omit [Nonempty α] in
/-- The event probability of a finite full-support PMF is the average of the
true normalized conditional event probabilities over the attained records. -/
theorem pmf_toMeasure_event_toReal_eq_sum
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) (E : Set α) :
    (p.toMeasure E).toReal =
      ∑ y : Set.range r,
        ((p.map (Set.rangeFactorization r)) y).toReal *
          ((p.filter {a | r a = y.1} (event_fiber_support p hp r y)).toMeasure E).toReal := by
  classical
  have hmeas : MeasurableSet E := MeasurableSet.of_discrete
  have hbind := congrArg (fun μ : PMF α => μ.toMeasure E)
    (pmf_eq_range_bind_filter p hp r)
  rw [PMF.toMeasure_bind_apply (p := p.map (Set.rangeFactorization r))
    (f := fun y => p.filter {a | r a = y.1} (event_fiber_support p hp r y))
    (s := E) hmeas] at hbind
  rw [tsum_fintype] at hbind
  have hfinite : ∀ y : Set.range r,
      (p.map (Set.rangeFactorization r)) y *
        (p.filter {a | r a = y.1} (event_fiber_support p hp r y)).toMeasure E ≠ ⊤ := by
    intro y
    let μ := (p.filter {a | r a = y.1} (event_fiber_support p hp r y)).toMeasure
    have : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hμtop : μ E ≠ ⊤ := ne_of_lt <| lt_of_le_of_lt
      (measure_mono (Set.subset_univ E)) (by rw [measure_univ]; exact ENNReal.one_lt_top)
    exact ENNReal.mul_ne_top
      ((p.map (Set.rangeFactorization r)).apply_ne_top y)
      hμtop
  rw [hbind, ENNReal.toReal_sum (fun y _ => hfinite y)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [ENNReal.toReal_mul]

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance eventConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance eventConfigNonempty : Nonempty (Configuration G) := ⟨∅⟩
local instance eventConfigMeasurableSpace : MeasurableSpace (Configuration G) := ⊤
local instance eventConfigDiscrete : DiscreteMeasurableSpace (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance eventConfigEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The FK event probability decomposes over the literal arbitrary-reveal
records; every conditional PMF is the genuine normalized fiber restriction. -/
theorem law_toMeasure_event_toReal_eq_sum_revealRecord
    (q : ClusterWeight) (ξ : BoundaryCondition V)
    (reveal : Configuration G → Configuration G) (E : Set (Configuration G)) :
    ((law G q ξ).toMeasure E).toReal =
      ∑ y : Set.range (revealRecordStatistic reveal),
        (((law G q ξ).map (Set.rangeFactorization (revealRecordStatistic reveal))) y).toReal *
          (((law G q ξ).filter
            {C | revealRecordStatistic reveal C = y.1}
            (event_fiber_support (law G q ξ)
              (fun C => (law_pos G q ξ C).ne') (revealRecordStatistic reveal) y)).toMeasure E).toReal := by
  exact pmf_toMeasure_event_toReal_eq_sum (law G q ξ)
    (fun C => (law_pos G q ξ C).ne') (revealRecordStatistic reveal) E
