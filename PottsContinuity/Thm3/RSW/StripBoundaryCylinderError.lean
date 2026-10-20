module

public import PottsContinuity.Thm3.RSW.StripCutCylinderComparison
public import PottsContinuity.Thm3.RSW.StripClosedCutFailure
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailureRecords
public import PottsContinuity.FKC.FiniteFK.RevealRecordBadEventBound
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open FKC.Medial FKC.FiniteFK
open PD.FK Exploration MeasureTheory Filter Topology
noncomputable section
local instance pdCutBoundaryRecordSpace (N n K : ℕ) : MeasurableSpace
    (Set.range (FKC.FiniteFK.revealRecordStatistic (horizontalStripClosedCutReveal N n K))) := ⊤

local instance pdCutBoundaryCylinderEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance pdCutBoundaryCylinderEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance pdCutBoundaryCylinderConfigFintype (N n : ℕ) :
    Fintype (PD.FK.Configuration (horizontalStripCutRectangle N n)) := Fintype.ofFinite _
local instance pdCutBoundaryCylinderConfigNonempty (N n : ℕ) :
    Nonempty (PD.FK.Configuration (horizontalStripCutRectangle N n)) := ⟨∅⟩
local instance pdCutBoundaryCylinderConfigMeasurable (N n : ℕ) :
    MeasurableSpace (PD.FK.Configuration (horizontalStripCutRectangle N n)) := ⊤
local instance pdCutBoundaryCylinderConfigDiscrete (N n : ℕ) :
    DiscreteMeasurableSpace (PD.FK.Configuration (horizontalStripCutRectangle N n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The actual finite rectangle cylinder is bounded by its canonical top-wired
infinite-volume cylinder probability plus the actual two-sided closed-cut
failure probability. -/
theorem strip_cylinder_boundary_le_topOnly_add_failure
    {N n K : ℕ} (hKN : K ≤ N) (q : Parameters)
    (ξ : PD.FK.BoundaryCondition (FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (F : Finset FKC.squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n))
 :
    (PD.FK.measure (horizontalStripCutRectangle N n) q ξ
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
      (PD.FK.measure (horizontalStripCutRectangle N n) q (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)) (horizontalStripRectangleCylinderEvent N n F)).toReal +
        (PD.FK.measure (horizontalStripCutRectangle N n) q ξ
          (horizontalStripClosedCutFailureEvent N n K)).toReal := by
  classical
  let G := horizontalStripCutRectangle N n
  let reveal : PD.FK.Configuration G → PD.FK.Configuration G :=
    fun A => horizontalStripClosedCutReveal N n K A
  let stat := FKC.FiniteFK.revealRecordStatistic reveal
  let bad := horizontalStripClosedCutBadRecordEvent N n K
  let E := horizontalStripRectangleCylinderEvent N n F
  let c : ℝ := (PD.FK.measure (horizontalStripCutRectangle N n) q (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)) (horizontalStripRectangleCylinderEvent N n F)).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hp : ∀ A : PD.FK.Configuration G, (PD.FK.law G q ξ) A ≠ 0 := by
    intro A
    exact (PD.FK.law_pos G q ξ A).ne'
  have hgood : ∀ y : Set.range stat, y ∉ bad →
      (((PD.FK.law G q ξ).filter {A | stat A = y.1}
        (by
          obtain ⟨A₀, hstat⟩ := y.2
          exact ⟨A₀, by simp [hstat], (PD.FK.law_pos G q ξ A₀).ne'⟩)).toMeasure E).toReal ≤ c := by
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
    have hcond := stripClosedCutRecord_cylinder_probability_le_topOnly
      hKN q ξ hξ hTop A₀ hL.symm hR.symm F
      (horizontalStripClosedCut_cylinder_edge_support hKN A₀ hL.symm hR.symm F hF)
    have hfiber : {A : PD.FK.Configuration G | stat A = y.1} =
        Exploration.revealRecordEvent reveal A₀ := by
      rw [← hstat]
      have hh := revealRecordStatistic_fiber_eq reveal A₀
      apply hh.trans
      ext C
      simp only [FKC.FiniteFK.revealRecordEvent,Exploration.revealRecordEvent,
        Set.mem_ofPred_eq,Finset.ext_iff,Finset.mem_inter]
    simpa [E, c, G, reveal, stat, hfiber] using hcond
  have havg := pmf_event_probability_le_good_record_bound_add_bad_mass
    (p := PD.FK.law G q ξ) hp stat bad E c hc hgood
  have hbad : (((PD.FK.law G q ξ).map (Set.rangeFactorization stat)).toMeasure bad).toReal =
      (PD.FK.measure G q ξ (horizontalStripClosedCutFailureEvent N n K)).toReal := by
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
    have heq : {A : PD.FK.Configuration G | Set.rangeFactorization stat A ∈ bad} =
        horizontalStripClosedCutFailureEvent N n K := by
      exact horizontalStripClosedCutBadRecord_preimage N n K hKN
    change ((PD.FK.law G q ξ).toMeasure {A | Set.rangeFactorization stat A ∈ bad}).toReal = _
    rw [heq]
    rfl
  change (PD.FK.measure G q ξ E).toReal ≤ c + _ at havg
  rw [hbad] at havg
  simpa [c, E, G] using havg

end
end PottsContinuity.RSW
