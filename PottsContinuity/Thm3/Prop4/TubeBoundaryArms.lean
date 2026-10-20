module

public import PottsContinuity.Thm3.Prop4.TubeSurgery
public import PottsContinuity.Foundations.BoxBoundary

/-!
# The n and n-1 endpoint arms in the same cut configuration

This module defines the primal endpoint-arm event `finiteEndpointArmEvent` used in
equation (32). For two disconnected endpoints in the same configuration, its
probability is bounded by the product of infinite one-arm probabilities in
`Thm3.Prop4.FiniteArmProduct` (`free_disconnected_endpoint_arms_le_infinite_product`).
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

attribute [local instance] PD.FK.configurationMeasurableSpace

local instance tubeBoundaryArmsEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- A genuine finite-box connection from the given center to its translated frozen boundary. -/
def finiteEndpointArmEvent (n : ℕ) (a : (box n : Set (ℤ × ℤ))) (r : ℕ) :
    Set (PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {A | ∃ z : (box n : Set (ℤ × ℤ)), z.val-a.val ∈ vertexBoundary (box r) ∧
    PD.FK.ActualConnected _ A a z}

end

end PottsContinuity.Thm3.Prop4
