module

public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.PlanarMixed.BoundaryMergeCost
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.PD.FK.RemainingComparison

/-!
# Conditional connection estimates on actual stopping records

The full stopped FK law is imported from `Exploration.FiniteStoppingSetDMP`. A
remaining-edge connection event with a mixed-RSW bound can be transported to any
actual target event by a record-wise deterministic inclusion. Source extremal-path selectors and the
geometric mixed-domain bound are required explicitly.
-/

@[expose] public section

namespace PottsContinuity.RSW

open MeasureTheory PD.FK Exploration

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance stoppedConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The stopped-law identity `law_filter_revealRecord_map_remaining` evaluated on any
remaining-edge event. -/
theorem revealRecord_remaining_probability (θ : Parameters) (ξ : BoundaryCondition V)
    (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) (D : Set (RemainingConfiguration G (reveal C₀))) :
    (((law G θ ξ).filter (revealRecordEvent reveal C₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
        exact frozenStateEvent_support θ ξ (reveal C₀)
          (revealRecordConfiguration reveal C₀))).toMeasure
      ((fun C => (configurationSplitEquiv G (reveal C₀) C).1) ⁻¹' D)) =
      (remainingLaw G θ (frozenBoundary ξ (revealRecordConfiguration reveal C₀).val)
        (reveal C₀)).toMeasure D := by
  have h := congrArg (fun ρ : PMF (RemainingConfiguration G (reveal C₀)) => ρ.toMeasure D)
    (law_filter_revealRecord_map_remaining θ ξ reveal hstable C₀)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at h
  exact h

/-- A remaining-edge estimate and an actual record-wise inclusion give the
conditional target estimate. The inclusion refers to actual sampled states;
virtual identifications in the induced partition do not enter the target event. -/
theorem stopped_connection_lower_of_remaining_bound
    (θ : Parameters) (ξ : BoundaryCondition V)
    (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) (D : Set (RemainingConfiguration G (reveal C₀)))
    (A : Set (Configuration G)) (c : ℝ)
    (hbound : c ≤ ((remainingLaw G θ
      (frozenBoundary ξ (revealRecordConfiguration reveal C₀).val)
        (reveal C₀)).toMeasure D).toReal)
    (hsurgery : ∀ C ∈ revealRecordEvent reveal C₀,
      (configurationSplitEquiv G (reveal C₀) C).1 ∈ D → C ∈ A) :
    c ≤ (((law G θ ξ).filter (revealRecordEvent reveal C₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
        exact frozenStateEvent_support θ ξ (reveal C₀)
          (revealRecordConfiguration reveal C₀))).toMeasure A).toReal := by
  let hs : ∃ C ∈ revealRecordEvent reveal C₀, C ∈ (law G θ ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
    exact frozenStateEvent_support θ ξ (reveal C₀)
      (revealRecordConfiguration reveal C₀)
  let ρ := (law G θ ξ).filter (revealRecordEvent reveal C₀) hs
  let E := (fun C => (configurationSplitEquiv G (reveal C₀) C).1) ⁻¹' D
  have hprob : ρ.toMeasure E = (remainingLaw G θ
      (frozenBoundary ξ (revealRecordConfiguration reveal C₀).val)
        (reveal C₀)).toMeasure D := revealRecord_remaining_probability θ ξ reveal hstable C₀ D
  have hrestrict : ρ.toMeasure E = ρ.toMeasure (E ∩ revealRecordEvent reveal C₀) := by
    apply PMF.toMeasure_apply_eq_of_inter_support_eq _
      MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
    ext C
    constructor
    · rintro ⟨hC, hρ⟩
      exact ⟨⟨hC, ((PMF.mem_support_filter_iff hs).mp hρ).1⟩, hρ⟩
    · rintro ⟨⟨hC, _⟩, hρ⟩
      exact ⟨hC, hρ⟩
  calc
    c ≤ (ρ.toMeasure E).toReal := by rw [hprob]; exact hbound
    _ = (ρ.toMeasure (E ∩ revealRecordEvent reveal C₀)).toReal := congrArg ENNReal.toReal hrestrict
    _ ≤ (ρ.toMeasure A).toReal := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      rintro C ⟨hD, hrecord⟩
      exact hsurgery C hrecord hD

end
end PottsContinuity.RSW
