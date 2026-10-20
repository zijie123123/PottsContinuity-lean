module

public import PottsContinuity.Critical.ThresholdMonotonicity
public import PottsContinuity.Critical.PathEventLimits
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.Infinite.Parameters
public import PottsContinuity.PD.FK.FreeBoxPositiveAssociation
public import PottsContinuity.PD.RCInfinite.Cylinders

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Coincidence

open PottsContinuity
open PottsContinuity.Critical
open PottsContinuity.Infinite
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open PottsContinuity.PD.FK.Internal
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance freeMonoBoxEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _

local instance freeMonoBoxEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (boxGraph c r).edgeSet := Classical.decEq _

attribute [local instance] configurationMeasurableSpace

private theorem boxProbabilityMeasure_apply_preimage (θ : Parameters)
    (c : LatticeVertex) (r : ℕ) (E : Set LatticeConfiguration)
    (hE : MeasurableSet E) :
    (boxProbabilityMeasure θ c r : Measure LatticeConfiguration) E =
      measure (boxGraph c r) θ (BoundaryCondition.free ∅)
        (boxConfiguration c r ⁻¹' E) := by
  change ((law (boxGraph c r) θ (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
  rfl

/-- Increasing events have monotone probabilities under the free finite-box
FK laws as the edge parameter increases. -/
theorem freeBoxProbabilityMeasure_parameter_mono (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (c : LatticeVertex) (r : ℕ) (E : Set LatticeConfiguration)
    (hE : MeasurableSet E) (hEinc : IsIncreasingConfigurationEvent E) :
    (boxProbabilityMeasure θ c r : Measure LatticeConfiguration) E ≤
      (boxProbabilityMeasure θ' c r : Measure LatticeConfiguration) E := by
  let ξ : BoundaryCondition (BoxVertex c r) := BoundaryCondition.free ∅
  let s := boxConfiguration c r ⁻¹' E
  have hs : IsUpperSet s := by
    intro A B hAB hA
    apply hEinc
    · intro e he
      exact boxConfiguration_mono c r hAB e he
    · exact hA
  have hf0 : ∀ A, 0 ≤ s.indicator (fun _ => (1 : ℝ)) A := by
    intro A
    by_cases hA : A ∈ s <;> simp [Set.indicator, hA]
  have hfm : Monotone (s.indicator (fun _ => (1 : ℝ))) := by
    intro A B hAB
    by_cases hA : A ∈ s
    · have hB := hs hAB hA
      simp [Set.indicator, hA, hB]
    · simp only [Set.indicator_of_notMem hA]
      exact hf0 B
  have hfinite := finite_fk_expectation_monotone θ θ' hq hp ξ
    (s.indicator (fun _ => (1 : ℝ))) hf0 hfm
  have hleft :
      ((boxProbabilityMeasure θ c r : Measure LatticeConfiguration).real E) =
        ∑ A, (s.indicator (fun _ => (1 : ℝ)) A) *
          configurationProbability (boxGraph c r) θ ξ A := by
    rw [Measure.real, boxProbabilityMeasure_apply_preimage θ c r E hE]
    calc
      (measure (boxGraph c r) θ ξ s).toReal =
          ∑ A, configurationProbability (boxGraph c r) θ ξ A *
            s.indicator (fun _ => (1 : ℝ)) A :=
        measure_toReal_eq_indicator_sum θ ξ s
      _ = ∑ A, s.indicator (fun _ => (1 : ℝ)) A *
            configurationProbability (boxGraph c r) θ ξ A := by
        apply Finset.sum_congr rfl
        intro A hA
        exact mul_comm _ _
  have hright :
      ((boxProbabilityMeasure θ' c r : Measure LatticeConfiguration).real E) =
        ∑ A, (s.indicator (fun _ => (1 : ℝ)) A) *
          configurationProbability (boxGraph c r) θ' ξ A := by
    rw [Measure.real, boxProbabilityMeasure_apply_preimage θ' c r E hE]
    calc
      (measure (boxGraph c r) θ' ξ s).toReal =
          ∑ A, configurationProbability (boxGraph c r) θ' ξ A *
            s.indicator (fun _ => (1 : ℝ)) A :=
        measure_toReal_eq_indicator_sum θ' ξ s
      _ = ∑ A, s.indicator (fun _ => (1 : ℝ)) A *
            configurationProbability (boxGraph c r) θ' ξ A := by
        apply Finset.sum_congr rfl
        intro A hA
        exact mul_comm _ _
  have hreal :
      (boxProbabilityMeasure θ c r : Measure LatticeConfiguration).real E ≤
        (boxProbabilityMeasure θ' c r : Measure LatticeConfiguration).real E := by
    rw [hleft, hright]
    exact hfinite
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- Free box limits preserve parameter monotonicity on clopen increasing
events. -/
theorem freeBoxLimit_parameter_mono_of_clopen (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (μ ν : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (hν : Tendsto (fun n => boxProbabilityMeasure θ' (0, 0) n) atTop (𝓝 ν))
    (E : Set LatticeConfiguration) (hE : IsClopen E)
    (hEinc : IsIncreasingConfigurationEvent E) : μ E ≤ ν E := by
  have hμE := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hE
  have hνE := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hE
  apply le_of_tendsto_of_tendsto hμE hνE
  filter_upwards with n
  have h := freeBoxProbabilityMeasure_parameter_mono θ θ' hq hp (0, 0) n E
    hE.isClosed.measurableSet hEinc
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact ENNReal.coe_le_coe.mp h

private theorem simpleOpenWalkCylinder_antitone :
    Antitone Critical.simpleOpenWalkCylinder := by
  intro m n hmn
  induction hmn with
  | refl => exact Set.Subset.rfl
  | @step n h ih =>
      exact (Critical.simpleOpenWalkCylinder_succ_subset n).trans ih

end

end PottsContinuity.Coincidence
