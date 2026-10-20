module

public import PottsContinuity.Thm3.Push.SameLabelClosedCut
public import PottsContinuity.Thm3.Push.IntervalArmFilledExploration
public import PottsContinuity.Thm3.Push.ClosedPathTransfer
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance armRegionClosedEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
local instance armRegionClosedPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every opposite-region vertex has a genuine CLOSED dual connection to an
opposite exterior seed in the complement of the actual filled frontier. The
geometric region path is not assumed to have closed states in the original A. -/
theorem intervalArmRightRegion_closed_frontier_connection
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmRightRegion N l r A) :
    ∃ b ∈ intervalArmRightDualPorts N r,
      ActualConnected (rectangleDualGraph (0,0) N N)
        (rectangleDualConfiguration (0,0) N N (intervalArmFilledLeftFrontier N l r A)) b v := by
  obtain ⟨b,hb,hbs,hvs,⟨q⟩⟩ := hv
  let S := intervalArmLeftReached N l A
  let R := intervalArmRightRegion N l r A
  let H := rectangleDualGraph (0,0) N N
  let σ := fun z => decide (z ∉ R)
  let inclusion : H.induce Sᶜ →g H := {toFun := Subtype.val,map_rel' := fun h => h}
  let qH := q.map inclusion
  have hsupport : ∀ z ∈ qH.support, z ∈ R := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    exact ⟨b,hb,hbs,t.property,(q.takeUntil t ht).reachable⟩
  let qR := qH.induce R hsupport
  have hlabel : ∀ z ∈ R, σ z=false := by
    intro z hz
    exact decide_eq_false (not_not_intro hz)
  have hc := constantLabelRegion_connected_in_closedCut
    (DualityExt.rectangleDualEdgeEquiv (0,0) N N) σ R false hlabel _ _ qR.reachable
  change ActualConnected H
    (auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
      (intervalArmFilledLeftFrontier N l r A)) b v at hc
  rw [auxiliaryClosedConfiguration_rectangle_eq] at hc
  exact ⟨b,hb,hc⟩

end
end PottsContinuity.Push
