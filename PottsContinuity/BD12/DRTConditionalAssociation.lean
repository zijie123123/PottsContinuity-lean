module

public import PottsContinuity.BD12.DRTAssociation
public import PottsContinuity.BD12.FiniteMonotoneSampler
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Conditional FKG and one-step conditional monotonicity for the actual
finite DRT weights, with arbitrary revealed edges and arbitrary revealed values. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtConditionalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance drtConditionalEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The positive DRT weight, retaining its strict positivity certificate. -/
def drtPositiveWeight (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (A : Configuration G) : Set.Ioi (0 : ℝ) :=
  ⟨drtWeight G q ξ J β A, drtWeight_pos G q ξ J β A⟩

end
end PottsContinuity.BD12
