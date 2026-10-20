-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutFailureRecords.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutRecordState
public import PottsContinuity.FKC.FiniteFK.RevealRecordEventDisintegration
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripClosedCutFailureRecordsEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripClosedCutFailureRecordsEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance horizontalStripClosedCutFailureRecordsConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripCutRectangle N n)) := Fintype.ofFinite _
local instance horizontalStripClosedCutFailureRecordsConfigNonempty (N n : ℕ) :
    Nonempty (Configuration (horizontalStripCutRectangle N n)) := ⟨∅⟩
local instance horizontalStripClosedCutFailureRecordsConfigMeasurable (N n : ℕ) :
    MeasurableSpace (Configuration (horizontalStripCutRectangle N n)) := ⊤
local instance horizontalStripClosedCutFailureRecordsConfigDiscrete (N n : ℕ) :
    DiscreteMeasurableSpace (Configuration (horizontalStripCutRectangle N n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance horizontalStripClosedCutFailureRecordsRangeFintype (N n K : ℕ) :
    Fintype (Set.range (revealRecordStatistic
      (horizontalStripClosedCutReveal N n K))) := Fintype.ofFinite _
local instance horizontalStripClosedCutFailureRecordsRangeMeasurable (N n K : ℕ) :
    MeasurableSpace (Set.range (revealRecordStatistic
      (horizontalStripClosedCutReveal N n K))) := ⊤
local instance horizontalStripClosedCutFailureRecordsRangeDiscrete (N n K : ℕ) :
    DiscreteMeasurableSpace (Set.range (revealRecordStatistic
      (horizontalStripClosedCutReveal N n K))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The actual two-sided cut-scan failure event in the finite FK rectangle. -/
def horizontalStripClosedCutFailureEvent (N n K : ℕ) :
    Set (Configuration (horizontalStripCutRectangle N n)) :=
  {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
    (horizontalStripRightBlockScan N n K A).2 = none}

/-- Attained records with at least one representative configuration having a
failed actual left or right scan. -/
def horizontalStripClosedCutBadRecordEvent (N n K : ℕ) :
    Set (Set.range (revealRecordStatistic (horizontalStripClosedCutReveal N n K))) :=
  {y | ∃ A : Configuration (horizontalStripCutRectangle N n),
    revealRecordStatistic (horizontalStripClosedCutReveal N n K) A = y.1 ∧
      A ∈ horizontalStripClosedCutFailureEvent N n K}

local instance horizontalStripClosedCutFailureRecordsBadDecidable (N n K : ℕ) :
    DecidablePred (fun y : Set.range (revealRecordStatistic
      (horizontalStripClosedCutReveal N n K)) =>
        y ∈ horizontalStripClosedCutBadRecordEvent N n K) := Classical.decPred _

theorem horizontalStripClosedCutBadRecord_iff_failure
    (N n K : ℕ) (hKN : K ≤ N)
    (A₀ : Configuration (horizontalStripCutRectangle N n)) :
    (⟨revealRecordStatistic (horizontalStripClosedCutReveal N n K) A₀,
      ⟨A₀, rfl⟩⟩ : Set.range (revealRecordStatistic
        (horizontalStripClosedCutReveal N n K))) ∈
        horizontalStripClosedCutBadRecordEvent N n K ↔
      A₀ ∈ horizontalStripClosedCutFailureEvent N n K := by
  constructor
  · rintro ⟨A, hA, hfail⟩
    have hstat : revealRecordStatistic (horizontalStripClosedCutReveal N n K) A =
        revealRecordStatistic (horizontalStripClosedCutReveal N n K) A₀ :=
      hA.trans rfl
    have hrecord : A ∈ revealRecordEvent (horizontalStripCutRectangle N n)
        (horizontalStripClosedCutReveal N n K) A₀ := by
      rw [← revealRecordStatistic_fiber_eq (horizontalStripClosedCutReveal N n K) A₀]
      exact hstat
    have hscans := horizontalStripClosedCutScans_eq_on_record N n K A A₀ hKN hrecord
    simpa [horizontalStripClosedCutFailureEvent, hscans.1, hscans.2] using hfail
  · intro hfail
    exact ⟨A₀, rfl, hfail⟩

theorem horizontalStripClosedCutBadRecord_preimage
    (N n K : ℕ) (hKN : K ≤ N) :
  {A : Configuration (horizontalStripCutRectangle N n) |
      Set.rangeFactorization (revealRecordStatistic
        (horizontalStripClosedCutReveal N n K)) A ∈
        horizontalStripClosedCutBadRecordEvent N n K} =
      horizontalStripClosedCutFailureEvent N n K := by
  ext A
  exact horizontalStripClosedCutBadRecord_iff_failure N n K hKN A

theorem horizontalStripClosedCutBadRecord_probability_eq
    (q : ClusterWeight) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (((law (horizontalStripCutRectangle N n) q ξ).map
      (Set.rangeFactorization (revealRecordStatistic
        (horizontalStripClosedCutReveal N n K)))).toMeasure
        (horizontalStripClosedCutBadRecordEvent N n K)).toReal =
    (measure (horizontalStripCutRectangle N n) q ξ
        (horizontalStripClosedCutFailureEvent N n K)).toReal := by
  change (((law (horizontalStripCutRectangle N n) q ξ).map
    (Set.rangeFactorization (revealRecordStatistic
      (horizontalStripClosedCutReveal N n K)))).toMeasure
      (horizontalStripClosedCutBadRecordEvent N n K)).toReal =
    ((law (horizontalStripCutRectangle N n) q ξ).toMeasure
      (horizontalStripClosedCutFailureEvent N n K)).toReal
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top]
  have hpre :
      (Set.rangeFactorization (revealRecordStatistic
        (horizontalStripClosedCutReveal N n K))) ⁻¹'
          horizontalStripClosedCutBadRecordEvent N n K =
        horizontalStripClosedCutFailureEvent N n K := by
    ext A
    exact horizontalStripClosedCutBadRecord_iff_failure N n K hKN A
  rw [hpre]

end
end PottsContinuity.FKC.Medial
