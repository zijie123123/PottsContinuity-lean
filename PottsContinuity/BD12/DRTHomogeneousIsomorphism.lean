module

public import PottsContinuity.BD12.DRTHomogeneousParameters
public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Relabelling invariance of every observable under the actual homogeneous
finite beta-law, with the boundary partition transported exactly. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
local instance homogeneousIsoInnerEdges : Fintype G.edgeSet := Fintype.ofFinite _
local instance homogeneousIsoOuterEdges : Fintype H.edgeSet := Fintype.ofFinite _

/-- Graph isomorphisms preserve the actual homogeneous finite law and every
observable, after exact transport of the boundary partition. -/
theorem drtMean_homogeneous_configurationIso (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (e : G ≃g H) (ξ : BoundaryCondition V) (β : Set.Ioi (0 : ℝ)) (f : Configuration H → ℝ) :
    drtMean H q (boundaryConditionIso e ξ)
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β f =
      drtMean G q ξ (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (fun C => f (configurationIso e C)) := by
  rw [drtMean_homogeneous_parameters_eq H q hq, drtMean_homogeneous_parameters_eq G q hq,
    ← law_configurationIso_map (drtHomogeneousParameters q hq β) e ξ,
    FiniteProbability.expectation_map]

end
end PottsContinuity.BD12
