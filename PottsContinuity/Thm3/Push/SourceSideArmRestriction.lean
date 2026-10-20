module

public import PottsContinuity.Thm3.Push.SourceSideArm
public import PottsContinuity.Thm3.Push.WalkIntervalExit

@[expose] public section

namespace PottsContinuity.Push
open PD.FK

/-- An original bottom arm reaching outside a narrower horizontal interval
has an original-bond prefix to one of its two sides, confined to that interval. -/
theorem sourceSquareSideArmEvent_subset_side_union
    (N : ℕ) (l r L₀ R₀ T L R : ℤ)
    (hl : L ≤ l) (hr : r ≤ R) (hT : T ≤ L ∨ R ≤ T) :
    sourceSquareSideArmEvent N l r L₀ R₀ T ⊆
      sourceSquareSideArmEvent N l r L R L ∪
        sourceSquareSideArmEvent N l r L R R := by
  intro C hC
  obtain ⟨a,b,p,ha,hal,har,hb,_hp⟩ := hC
  have hstep : ∀ {u v : RectangleVertex (0,0) N N},
      (openGraph (rectangleGraph (0,0) N N) C).Adj u v →
        u.val.1 - 1 ≤ v.val.1 ∧ v.val.1 ≤ u.val.1 + 1 := by
    intro u v huv
    have h := openGraph_le _ C huv
    change |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1 at h
    have hnonneg := abs_nonneg (u.val.2-v.val.2)
    have habs := abs_le.mp (show |u.val.1-v.val.1| ≤ 1 by omega)
    omega
  obtain ⟨z,q,hz,hq,_⟩ := walk_exists_interval_exit (fun w => w.val.1)
    hstep L R p ⟨by omega,by omega⟩ (by simpa only [hb] using hT)
  rcases hz with hz | hz
  · exact Or.inl ⟨a,z,q,ha,hal,har,hz,hq⟩
  · exact Or.inr ⟨a,z,q,ha,hal,har,hz,hq⟩

end PottsContinuity.Push
