module

public import PottsContinuity.Thm3.Push.IntervalArmRegionClosedConnections
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Any actual filled-frontier source arm excludes the entire opposite
geometric region from the exterior arc BEFORE its own bottom root. -/
theorem intervalArmRightRegion_avoids_left_of_frontier_root
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Walk s t)
    (hs : s.val.2=0) (ht : t.val.2=(N : ℤ)) (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    (d : RectangleDualVertex (0,0) N N) (hd : d ∈ intervalArmLeftDualPorts N s.val.1) :
    d ∉ intervalArmRightRegion N l r A := by
  intro hdR
  obtain ⟨b,hb,hbd⟩ := intervalArmRightRegion_closed_frontier_connection N l r A d hdR
  have hb' : b ∈ intervalArmRightDualPorts N s.val.1 := by
    rcases (mem_intervalArmRightDualPorts N r b).mp hb with hb | ⟨hb,hrb⟩
    · exact (mem_intervalArmRightDualPorts N s.val.1 b).mpr (Or.inl hb)
    · exact (mem_intervalArmRightDualPorts N s.val.1 b).mpr (Or.inr ⟨hb,by omega⟩)
  exact interval_arm_excludes_complementary_dual_connection N s.val.1 s.val.1
    (by omega) le_rfl (by omega) (intervalArmFilledLeftFrontier N l r A)
    p hs ht le_rfl le_rfl hd hb' hbd.symm

end
end PottsContinuity.Push
