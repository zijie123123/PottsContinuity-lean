module

public import PottsContinuity.Thm3.Push.IntervalArmDualSeparation
public import PottsContinuity.Thm3.Push.RectangleLabelFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance intervalLeftPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance intervalLeftEdgeDecidableEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- Explore the actual closed dual clusters from the source left/bottom-left
arc. The recorded states are those of the original primal square. -/
abbrev intervalArmLeftReveal (N : ℕ) (l : ℤ) :=
  closedClusterReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N) (intervalArmLeftDualPorts N l)

/-- The true-dual vertices reached by this concrete source exploration. -/
abbrev intervalArmLeftReached (N : ℕ) (l : ℤ) :=
  closedClusterReached (DualityExt.rectangleDualEdgeEquiv (0,0) N N) (intervalArmLeftDualPorts N l)

/-- The entire actual primal boundary of the reached dual region. No path
witness has yet been selected from this set of open original bonds. -/
def intervalArmLeftFrontier (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    Configuration (rectangleGraph (0,0) N N) :=
  auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
    (fun z => decide (z ∈ intervalArmLeftReached N l A))

/-- Every designated left/bottom-left seed belongs to the explored region. -/
theorem intervalArmLeftReached_contains_seed (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N))
    {b : RectangleDualVertex (0,0) N N} (hb : b ∈ intervalArmLeftDualPorts N l) :
    b ∈ intervalArmLeftReached N l A := ⟨b,hb,SimpleGraph.Reachable.rfl⟩

/-- On the actual source arm event the exploration cannot touch a right or
bottom-right seed. This is proved from sampled primal/dual separation. -/
theorem intervalArmLeftReached_avoids_right_of_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    {d : RectangleDualVertex (0,0) N N} (hd : d ∈ intervalArmRightDualPorts N r) :
    d ∉ intervalArmLeftReached N l A := by
  rintro ⟨b,hb,hbd⟩
  rw [auxiliaryClosedConfiguration_rectangle_eq] at hbd
  exact interval_arm_excludes_complementary_dual_connection N l r hl hlr hr A p
    hs ht hsl hsr hb hd hbd

/-- Every bond of the concrete source frontier is open and recorded. -/
theorem intervalArmLeftFrontier_subset_open_record (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmLeftFrontier N l A ⊆ A ∩ intervalArmLeftReveal N l A :=
  reached_labelCut_subset_open_and_revealed _ _ A

/-- The concrete source reveal satisfies stopping locality on its whole
configuration carrier, whether or not an interval arm exists. -/
theorem intervalArmLeftReveal_stable (N : ℕ) (l : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmLeftReveal N l A = A ∩ intervalArmLeftReveal N l A) :
    intervalArmLeftReveal N l B = intervalArmLeftReveal N l A :=
  closedClusterReveal_stable _ _ A B hstates

/-- The reached true-dual region is fixed on each complete original record. -/
theorem intervalArmLeftReached_eq_of_record_agreement (N : ℕ) (l : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmLeftReveal N l A = A ∩ intervalArmLeftReveal N l A) :
    intervalArmLeftReached N l B = intervalArmLeftReached N l A :=
  closedClusterReached_eq_of_reveal_agreement _ _ A B hstates

end
end PottsContinuity.Push
