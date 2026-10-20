module

public import PottsContinuity.BD12.DRTHomogeneousParameters
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Actual finite event probabilities as means under the homogeneous beta-law. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance eventProbabilityEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- The FK event measure is its literal PMF indicator expectation. -/
theorem fk_finite_event_expectation_eq_probability (θ : Parameters) (ξ : BoundaryCondition V)
    (A : Set (Configuration G)) :
    FiniteProbability.expectation (law G θ ξ) (A.indicator (fun _ => (1 : ℝ))) =
      (measure G θ ξ A).toReal := by
  rw [measure_toReal_eq_indicator_sum]
  simp only [FiniteProbability.expectation, law_apply,
    ENNReal.toReal_ofReal (configurationProbability_pos G θ ξ _).le]

/-- The physical parameter bridge preserves every event probability. -/
theorem drt_mean_indicator_eq_fk_probability (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (β : Set.Ioi (0 : ℝ)) (A : Set (Configuration G)) :
    drtMean G q ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (A.indicator (fun _ => (1 : ℝ))) =
      (measure G (drtHomogeneousParameters q hq β) ξ A).toReal := by
  rw [drtMean_homogeneous_parameters_eq]
  exact fk_finite_event_expectation_eq_probability G _ ξ A

end
end PottsContinuity.BD12
