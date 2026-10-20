module

public import PottsContinuity.Thm3.Push.IntervalArmRecord

@[expose] public section

namespace PottsContinuity.Push
open PD.FK

/-- Original source-square bottom-to-top arm confined between two specified
vertical sides. This uses only original open bonds, including boundary bonds. -/
def sourceSquareTopArmEvent (N : ℕ) (l r L R : ℤ) :
    Set (Configuration (rectangleGraph (0,0) N N)) :=
  {C | ∃ a b : RectangleVertex (0,0) N N,
    ∃ p : (openGraph (rectangleGraph (0,0) N N) C).Walk a b,
      a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧ b.val.2 = (N:ℤ) ∧
      ∀ w ∈ p.support, L ≤ w.val.1 ∧ w.val.1 ≤ R}

/-- Opening original bonds preserves the confined top arm. -/
theorem sourceSquareTopArmEvent_isUpperSet (N : ℕ) (l r L R : ℤ) :
    IsUpperSet (sourceSquareTopArmEvent N l r L R) := by
  intro C C' hCC' hC
  obtain ⟨a,b,p,ha,hal,har,hb,hp⟩ := hC
  refine ⟨a,b,p.mapLe (openGraph_mono hCC'),ha,hal,har,hb,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hw
  exact hp w hw

/-- Forgetting confinement gives the actual interval-to-top event in the
original square, without adding any wired connection. -/
theorem sourceSquareTopArmEvent_subset_intervalArmEvent (N : ℕ) (l r L R : ℤ) :
    sourceSquareTopArmEvent N l r L R ⊆ intervalArmEvent N l r := by
  rintro C ⟨a,b,p,ha,hal,har,hb,_⟩
  exact ⟨a,⟨ha,hal,har⟩,b,hb,⟨p⟩⟩

end PottsContinuity.Push
