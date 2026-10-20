module

public import PottsContinuity.Critical.FiniteMonotonicity
public import PottsContinuity.Critical.DualCircuitCounting
public import PottsContinuity.PD.FK.WiredBoxLimits
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace PottsContinuity.Critical

open MeasureTheory
open Filter Topology
open PottsContinuity.PD.FK

noncomputable section

local instance thresholdBoxEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _

local instance thresholdBoxEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (boxGraph c r).edgeSet := Classical.decEq _

/-- An event on the whole-lattice configuration space that is increasing in
every edge state. -/
def IsIncreasingConfigurationEvent (E : Set LatticeConfiguration) : Prop :=
  ∀ ⦃ω ω'⦄, (∀ e, ω e = true → ω' e = true) → ω ∈ E → ω' ∈ E

private theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ⊆ B) (e : LatticeEdge)
    (hA : wiredBoxConfiguration c r A e = true) :
    wiredBoxConfiguration c r B e = true := by
  rw [wiredBoxConfiguration_open_iff] at hA ⊢
  intro f hf
  exact hAB (hA f hf)

private theorem wiredBox_preimage_upper (c : LatticeVertex) (r : ℕ)
    (E : Set LatticeConfiguration) (hE : IsIncreasingConfigurationEvent E) :
    IsUpperSet (wiredBoxConfiguration c r ⁻¹' E) := by
  intro A B hAB hA
  apply hE
  · intro e he
    exact wiredBoxConfiguration_mono c r hAB e he
  · exact hA

/-- A wired box probability of a measurable event is the finite FK law of its
preimage under the genuine wired extension. -/
theorem wiredBoxProbabilityMeasure_apply_preimage (θ : Parameters)
    (c : LatticeVertex) (r : ℕ) (E : Set LatticeConfiguration)
    (hE : MeasurableSet E) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) E =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        (wiredBoxConfiguration c r ⁻¹' E) := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
  rfl

/-- At fixed cluster weight, wired finite-box probabilities of any increasing
measurable event are monotone in the edge parameter. -/
theorem wiredBoxProbabilityMeasure_parameter_mono (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (c : LatticeVertex) (r : ℕ) (E : Set LatticeConfiguration)
    (hE : MeasurableSet E) (hEinc : IsIncreasingConfigurationEvent E) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) E ≤
      (wiredBoxProbabilityMeasure θ' c r : Measure LatticeConfiguration) E := by
  let ξ := BoundaryCondition.wired (boxVertexBoundary c r)
  let s := wiredBoxConfiguration c r ⁻¹' E
  have hs : IsUpperSet s := wiredBox_preimage_upper c r E hEinc
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
      ((wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real E) =
        ∑ A, (s.indicator (fun _ => (1 : ℝ)) A) * configurationProbability
          (boxGraph c r) θ ξ A := by
    rw [Measure.real, wiredBoxProbabilityMeasure_apply_preimage θ c r E hE]
    simpa only [mul_comm] using measure_toReal_eq_indicator_sum θ ξ s
  have hright :
      ((wiredBoxProbabilityMeasure θ' c r : Measure LatticeConfiguration).real E) =
        ∑ A, (s.indicator (fun _ => (1 : ℝ)) A) * configurationProbability
          (boxGraph c r) θ' ξ A := by
    rw [Measure.real, wiredBoxProbabilityMeasure_apply_preimage θ' c r E hE]
    simpa only [mul_comm] using measure_toReal_eq_indicator_sum θ' ξ s
  have hreal :
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real E ≤
        (wiredBoxProbabilityMeasure θ' c r : Measure LatticeConfiguration).real E := by
    rw [hleft, hright]
    exact hfinite
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- Parameter monotonicity passes to any pair of weak wired box limits on a
clopen increasing event. -/
theorem wiredBoxLimit_parameter_mono_of_clopen (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (μ ν : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (hν : Tendsto (fun n => wiredBoxProbabilityMeasure θ' (0, 0) n) atTop (𝓝 ν))
    (E : Set LatticeConfiguration) (hE : IsClopen E)
    (hEinc : IsIncreasingConfigurationEvent E) :
    μ E ≤ ν E := by
  have hμE := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hE
  have hνE := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hE
  apply le_of_tendsto_of_tendsto hμE hνE
  filter_upwards with n
  have h := wiredBoxProbabilityMeasure_parameter_mono θ θ' hq hp
    (0, 0) n E hE.isClosed.measurableSet hEinc
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact ENNReal.coe_le_coe.mp h

end
end PottsContinuity.Critical
