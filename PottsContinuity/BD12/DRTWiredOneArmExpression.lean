module

public import PottsContinuity.BD12.DRTWiredSourceGrowth
public import PottsContinuity.BD12.DRTPartialSumDecay
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The explicit finite quotient as a real function for differentiation.
It agrees with the physical wired mean on every positive argument. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical
local instance armExpressionEdges (n : ℕ) : Fintype (boxGraph (0,0) (2*n)).edgeSet := Fintype.ofFinite _

/-- The source's explicit quotient of finite weighted sums, for real arguments. -/
def drtWiredOneArmExpression (q : Set.Ioi (0 : ℝ)) (n : ℕ) (t : ℝ) : ℝ :=
  let H := boxGraph (0,0) (2*n)
  let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let ξ := BoundaryCondition.wired (boxVertexBoundary (0,0) (2*n))
  let X := boxOuterOneArmIndicator (0,0) n (2*n)
  (∑ C, drtWeight H q ξ J t C * X C) / ∑ C, drtWeight H q ξ J t C

@[simp] theorem drtWiredOneArmExpression_coe (q : Set.Ioi (0 : ℝ))
    (n : ℕ) (β : Set.Ioi (0 : ℝ)) :
    drtWiredOneArmExpression q n β = drtWiredOneArmMean q β n := rfl

/-- The physical finite quotient is differentiable at every positive argument. -/
theorem drtWiredOneArmExpression_differentiableAt (q : Set.Ioi (0 : ℝ))
    (n : ℕ) (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ (drtWiredOneArmExpression q n) t :=
  (drtMean_hasDerivAt_score_corrected _ q _ _ ⟨t,ht⟩ _).differentiableAt

/-- Actual partial sums of the real expressions equal the physical source sums. -/
@[simp] theorem drtWiredOneArmExpression_partialSum (q : Set.Ioi (0 : ℝ))
    (n : ℕ) (β : Set.Ioi (0 : ℝ)) :
    drtPartialSum (drtWiredOneArmExpression q) n β = drtWiredOneArmSum q β n := rfl

end
end PottsContinuity.BD12
