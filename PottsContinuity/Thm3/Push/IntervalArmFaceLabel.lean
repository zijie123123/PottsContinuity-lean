module

public import PottsContinuity.Thm3.Push.IntervalArmLeftExploration
public import PottsContinuity.PD.Duality.RectangleDualCrossing
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance intervalFacePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The expanded true-dual face carrier is literally the enlarged rectangle
of face bases. This equivalence preserves every integer coordinate. -/
def squareExpandedFaceEquiv (N : ℕ) : RectangleDualVertex (0,0) N N ≃
    RectangleVertex (-1,-1) (N+1) (N+1) := Equiv.refl _

/-- The reached-source label on the enlarged rectangle of true-dual faces. -/
def intervalArmFaceLabel (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N))
    (v : RectangleVertex (-1,-1) (N+1) (N+1)) : Bool :=
  decide ((squareExpandedFaceEquiv N).symm v ∈ intervalArmLeftReached N l A)

/-- All left boundary face vertices carry the reached-source label. -/
theorem intervalArmFaceLabel_left (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N))
    (v : RectangleVertex (-1,-1) (N+1) (N+1)) (hv : v.val.1 = -1) :
    intervalArmFaceLabel N l A v = true := by
  apply decide_eq_true
  apply intervalArmLeftReached_contains_seed N l A
  apply (mem_intervalArmLeftDualPorts N l _).mpr
  exact Or.inl hv

/-- The original open arm forces the opposite face boundary to carry the
unreached label. Its top endpoint is unrestricted. -/
theorem intervalArmFaceLabel_right_of_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    (v : RectangleVertex (-1,-1) (N+1) (N+1)) (hv : v.val.1 = (N : ℤ)) :
    intervalArmFaceLabel N l A v = false := by
  apply decide_eq_false
  exact intervalArmLeftReached_avoids_right_of_arm N l r hl hlr hr A p hs ht hsl hsr
    ((mem_intervalArmRightDualPorts N r _).mpr (Or.inl hv))

end
end PottsContinuity.Push
