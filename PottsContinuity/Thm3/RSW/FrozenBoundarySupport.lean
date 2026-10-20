module

public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.PD.FK.ComponentBoundarySupport
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- The exact induced frozen partition with its actual possible support:
original boundary vertices and endpoints of recorded open bonds. -/
def frozenBoundaryWithSupport {V : Type*} {G : SimpleGraph V}
    (ξ : BoundaryCondition V) (K : Configuration G) (D : Set V)
    (hD : ∀ ⦃e : G.edgeSet⦄, e ∈ K → ∀ ⦃v : V⦄, v ∈ e.val → v ∈ D) :
    BoundaryCondition V where
  boundary := ξ.boundary ∪ D
  partition := (frozenBoundary ξ K).partition
  supported := by
    intro x y hxy
    exact componentSetoid_le_wired_union_of_edge_endpoints ξ D K hD hxy

end PottsContinuity.RSW
