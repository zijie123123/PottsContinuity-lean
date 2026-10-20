module

public import PottsContinuity.BD12.DRTHomogeneousBridge
public import PottsContinuity.PD.FK.Expectation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! The actual homogeneous physical parameter map beta -> 1-exp(-beta),
including equality of the finite laws and of every finite observable's mean. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section

/-- Interior FK parameters associated with the homogeneous inverse temperature. -/
def drtHomogeneousParameters (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) : Parameters where
  val := q.val
  property := hq
  edgeProbability := ⟨1 - Real.exp (-(β : ℝ)), by
    constructor
    · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos β.property))
    · exact sub_lt_self _ (Real.exp_pos _)⟩

@[simp] theorem drtHomogeneousParameters_edgeParameter (q : Set.Ioi (0 : ℝ))
    (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    edgeParameter (drtHomogeneousParameters q hq β) = 1 - Real.exp (-(β : ℝ)) := rfl

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance homogeneousParameterEdges : Fintype G.edgeSet := Fintype.ofFinite _

/-- The beta-law is the existing finite FK law at the actual physical parameter. -/
theorem drtLaw_homogeneous_parameters_eq (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (β : Set.Ioi (0 : ℝ)) :
    drtLaw G q ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β = law G (drtHomogeneousParameters q hq β) ξ :=
  drtLaw_homogeneous_eq G (drtHomogeneousParameters q hq β) ξ β rfl

/-- Equality holds for every observable on the whole configuration carrier. -/
theorem drtMean_homogeneous_parameters_eq (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ) :
    drtMean G q ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β f =
      FiniteProbability.expectation (law G (drtHomogeneousParameters q hq β) ξ) f := by
  rw [drtMean_eq_sum_law, drtLaw_homogeneous_parameters_eq G q hq ξ β]
  rfl

end
end PottsContinuity.BD12
