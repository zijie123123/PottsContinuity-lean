-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutCylinderBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutConditionalCylinders
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailureRecords
public import PottsContinuity.FKC.FiniteFK.RevealRecordBadEventBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripSourceEventWeakLimit
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripClosedCutCylinderBoundEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripClosedCutCylinderBoundEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance horizontalStripClosedCutCylinderBoundConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripCutRectangle N n)) := Fintype.ofFinite _
local instance horizontalStripClosedCutCylinderBoundConfigNonempty (N n : ℕ) :
    Nonempty (Configuration (horizontalStripCutRectangle N n)) := ⟨∅⟩
local instance horizontalStripClosedCutCylinderBoundConfigMeasurable (N n : ℕ) :
    MeasurableSpace (Configuration (horizontalStripCutRectangle N n)) := ⊤
local instance horizontalStripClosedCutCylinderBoundConfigDiscrete (N n : ℕ) :
    DiscreteMeasurableSpace (Configuration (horizontalStripCutRectangle N n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The actual finite rectangle cylinder is bounded by its canonical top-wired
infinite-volume cylinder probability plus the actual two-sided closed-cut
failure probability. -/
theorem horizontalStripClosedCut_cylinder_probability_le_limit_add_failure
    {N n K : ℕ} (hKN : K ≤ N) (q : PottsContinuity.FKC.ClusterWeight)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n))
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    (measure (horizontalStripCutRectangle N n) q ξ
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ) +
        (measure (horizontalStripCutRectangle N n) q ξ
          (horizontalStripClosedCutFailureEvent N n K)).toReal := by
  classical
  let G := horizontalStripCutRectangle N n
  let reveal : Configuration G → Configuration G :=
    fun A => horizontalStripClosedCutReveal N n K A
  let stat := revealRecordStatistic reveal
  let bad := horizontalStripClosedCutBadRecordEvent N n K
  let E := horizontalStripRectangleCylinderEvent N n F
  let c : ℝ := ((μ (LatticeConfiguration.allOpen F) : NNReal) : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; exact NNReal.coe_nonneg _
  have hp : ∀ A : Configuration G, (law G q ξ) A ≠ 0 := by
    intro A
    exact (law_pos G q ξ A).ne'
  have hgood : ∀ y : Set.range stat, y ∉ bad →
      (((law G q ξ).filter {A | stat A = y.1}
        (by
          obtain ⟨A₀, hstat⟩ := y.2
          exact ⟨A₀, by simp [hstat], (law_pos G q ξ A₀).ne'⟩)).toMeasure E).toReal ≤ c := by
    intro y hybad
    obtain ⟨A₀, hstat⟩ := y.2
    have hyEq : y = ⟨stat A₀, ⟨A₀, rfl⟩⟩ := by
      apply Subtype.ext
      exact hstat.symm
    have hnotfail : A₀ ∉ horizontalStripClosedCutFailureEvent N n K := by
      intro hf
      have hbad : (⟨stat A₀, ⟨A₀, rfl⟩⟩ : Set.range stat) ∈ bad := by
        exact (horizontalStripClosedCutBadRecord_iff_failure N n K hKN A₀).2 hf
      exact hybad (by simpa [bad, hyEq] using hbad)
    have hLnot : (horizontalStripLeftBlockScan N n K A₀).2 ≠ none := by
      intro hnone
      exact hnotfail (Or.inl hnone)
    have hRnot : (horizontalStripRightBlockScan N n K A₀).2 ≠ none := by
      intro hnone
      exact hnotfail (Or.inr hnone)
    obtain ⟨i, hL⟩ := Option.ne_none_iff_exists.mp hLnot
    obtain ⟨j, hR⟩ := Option.ne_none_iff_exists.mp hRnot
    have hcond := horizontalStripClosedCutRecord_cylinder_probability_le_limit_of_center_support
      hKN q ξ hξ hTop A₀ hL.symm hR.symm F hF μ hμ
    have hfiber : {A : Configuration G | stat A = y.1} =
        revealRecordEvent G reveal A₀ := by
      rw [← hstat]
      simpa [stat] using (revealRecordStatistic_fiber_eq reveal A₀)
    simpa [E, c, G, reveal, stat, hfiber] using hcond
  have havg := pmf_event_probability_le_good_record_bound_add_bad_mass
    (p := law G q ξ) hp stat bad E c hc hgood
  have hbad := horizontalStripClosedCutBadRecord_probability_eq q N n K hKN ξ
  change (measure G q ξ E).toReal ≤ c + _ at havg
  rw [hbad] at havg
  simpa [c, E, G] using havg

end
end PottsContinuity.FKC.Medial
