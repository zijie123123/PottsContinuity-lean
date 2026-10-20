module

public import PottsContinuity.Thm3.Push.IntervalArmRecord
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Actual source-square arm with its original bottom interval and complete
horizontal confinement. The target is the specified vertical line. -/
def sourceSquareSideArmEvent (N : ℕ) (l r L R T : ℤ) :
    Set (Configuration (rectangleGraph (0,0) N N)) :=
  {C | ∃ a b : RectangleVertex (0,0) N N,
    ∃ p : (openGraph (rectangleGraph (0,0) N N) C).Walk a b,
      a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧ b.val.1 = T ∧
      ∀ w ∈ p.support, L ≤ w.val.1 ∧ w.val.1 ≤ R}

/-- Increasing actual bond states preserves the original confined arm. -/
theorem sourceSquareSideArmEvent_isUpperSet (N : ℕ) (l r L R T : ℤ) :
    IsUpperSet (sourceSquareSideArmEvent N l r L R T) := by
  intro C C' hCC' hC
  obtain ⟨a,b,p,ha,hal,har,hb,hp⟩ := hC
  refine ⟨a,b,p.mapLe (openGraph_mono hCC'),ha,hal,har,hb,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hw
  exact hp w hw

/-- The first arm in source Case 2, confined to R=[0,9s] x [0,2n]. -/
abbrev sourceCaseTwoFirstArm (n s : ℕ) :=
  sourceSquareSideArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) (9*(s:ℤ))

/-- The second arm, confined to R'=[4s,9s] x [0,2n], ending on its left side. -/
abbrev sourceCaseTwoSecondArm (n s : ℕ) :=
  sourceSquareSideArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ)) (4*(s:ℤ)) (9*(s:ℤ)) (4*(s:ℤ))

end
end PottsContinuity.Push
