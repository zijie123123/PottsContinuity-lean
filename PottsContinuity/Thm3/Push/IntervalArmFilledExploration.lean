module

public import PottsContinuity.Thm3.Push.IntervalArmLeftExploration
public import PottsContinuity.Thm3.Push.FilledFrontierDMP
public import PottsContinuity.Thm3.Push.JointStoppingReveal
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance intervalFilledPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance intervalFilledEdgeDecidableEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- Complementary true-dual components which meet the opposite exterior arc.
Components not meeting that arc are filled into the explored left region. -/
def intervalArmRightRegion (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) : Set (RectangleDualVertex (0,0) N N) :=
  outsideSeedRegion (rectangleDualGraph (0,0) N N)
    (intervalArmLeftReached N l A) (intervalArmRightDualPorts N r)

/-- Original primal bonds on the boundary of the filled source region. -/
def intervalArmFilledLeftFrontier (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) : Configuration (rectangleGraph (0,0) N N) :=
  auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
    (fun v => decide (v ∉ intervalArmRightRegion N l r A))

/-- Record every original bond incident to the filled left face region. -/
def intervalArmFilledLeftReveal (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) : Configuration (rectangleGraph (0,0) N N) :=
  auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
    (intervalArmRightRegion N l r A)ᶜ

/-- Filling removes boundary bonds and never creates a new sampled frontier. -/
theorem intervalArmFilledLeftFrontier_subset_raw (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmFilledLeftFrontier N l r A ⊆ intervalArmLeftFrontier N l A :=
  filled_region_labelCut_subset _ _ _

/-- Every filled source-frontier bond is actually open and originally read. -/
theorem intervalArmFilledLeftFrontier_subset_open_raw_record (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmFilledLeftFrontier N l r A ⊆ A ∩ intervalArmLeftReveal N l A :=
  (intervalArmFilledLeftFrontier_subset_raw N l r A).trans
    (intervalArmLeftFrontier_subset_open_record N l A)

/-- The original stopping reveal is contained in the filled reveal. -/
theorem intervalArmLeftReveal_subset_filled (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmLeftReveal N l A ⊆ intervalArmFilledLeftReveal N l r A := by
  intro e he
  obtain ⟨v,hv,hreached⟩ := (mem_closedClusterReveal_iff_endpoint _ _ A e).mp he
  apply (mem_auxiliaryRegionReveal _ _ e).mpr
  exact ⟨v,hv,fun hright => (outsideSeedRegion_subset_compl _ _ _ hright) hreached⟩

/-- The filled right region is fixed by agreement on the raw original record. -/
theorem intervalArmRightRegion_eq_of_raw_record_agreement (N : ℕ) (l r : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmLeftReveal N l A = A ∩ intervalArmLeftReveal N l A) :
    intervalArmRightRegion N l r B = intervalArmRightRegion N l r A :=
  congrArg (fun S => outsideSeedRegion (rectangleDualGraph (0,0) N N) S (intervalArmRightDualPorts N r))
    (intervalArmLeftReached_eq_of_record_agreement N l A B hstates)

/-- Filled source stopping locality holds on the complete configuration carrier. -/
theorem intervalArmFilledLeftReveal_stable (N : ℕ) (l r : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmFilledLeftReveal N l r A = A ∩ intervalArmFilledLeftReveal N l r A) :
    intervalArmFilledLeftReveal N l r B = intervalArmFilledLeftReveal N l r A := by
  have hsmall := recorded_agreement_of_subset A B _ _ (intervalArmLeftReveal_subset_filled N l r A) hstates
  exact congrArg (fun C => auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N) Cᶜ)
    (intervalArmRightRegion_eq_of_raw_record_agreement N l r A B hsmall)

/-- Right exterior seeds lie in the complementary region on the source arm
occurrence, by the proved actual primal/dual separation. -/
theorem intervalArmRightRegion_contains_seed_of_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N} (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ)) (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    {d : RectangleDualVertex (0,0) N N} (hd : d ∈ intervalArmRightDualPorts N r) :
    d ∈ intervalArmRightRegion N l r A :=
  mem_outsideSeedRegion_of_seed _ _ _ hd
    (intervalArmLeftReached_avoids_right_of_arm N l r hl hlr hr A p hs ht hsl hsr hd)

end
end PottsContinuity.Push
