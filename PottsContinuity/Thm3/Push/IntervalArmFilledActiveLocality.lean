module

public import PottsContinuity.Thm3.Push.SquareRegionActiveLocality
public import PottsContinuity.Thm3.Push.IntervalArmFilledExploration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- The filled frontier is the literal cut of the complementary true-dual
region. Boolean-label proofs are independent of their decision procedures. -/
theorem intervalArmFilledLeftFrontier_eq_squareRegionFrontier
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmFilledLeftFrontier N l r A =
      squareRegionFrontier N (intervalArmRightRegion N l r A)ᶜ := by
  unfold squareRegionFrontier intervalArmFilledLeftFrontier
  congr 1
  funext v
  exact decide_eq_decide.mpr Iff.rfl

end
end PottsContinuity.Push
