module

public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import PottsContinuity.FKC.FiniteFK.FrozenBoundaryOutsideRegion
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- Reuse the shared combinatorial boundary record with exactly the same
carrier, designated vertices and partition; no probability parameter occurs. -/
def boundaryConditionToFKC {V : Type*} (ξ : BoundaryCondition V) : FKC.FiniteFK.BoundaryCondition V where
  boundary := ξ.boundary
  partition := ξ.partition
  supported := ξ.supported

/-- When all frozen open edges lie away from an embedded domain, the retained
partition is exactly the original wired portion. The shared combinatorial
proof applies to every PD boundary without a cluster-weight restriction. -/
theorem frozenAway_partition_eq_wired {V U : Type*} {G : SimpleGraph V}
    (f : U ↪ V) (D W : Set V) (ξ : BoundaryCondition V) (A : Configuration G)
    (hξ : ξ.boundary ⊆ D ∪ W)
    (hW : (BoundaryCondition.wired W).partition ≤ ξ.partition)
    (hA : ∀ ⦃e : G.edgeSet⦄, e ∈ A → ∀ ⦃u : V⦄, u ∈ e.val → u ∈ D)
    (hf : ∀ u : U, f u ∉ D) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ A)).partition =
      (BoundaryCondition.wired (f ⁻¹' W)).partition := by
  exact FKC.FiniteFK.isolatedExtensionPullback_frozenBoundary_partition_eq_wired_away
    f D W (boundaryConditionToFKC ξ) A hξ hW hA hf

end PottsContinuity.RSW
