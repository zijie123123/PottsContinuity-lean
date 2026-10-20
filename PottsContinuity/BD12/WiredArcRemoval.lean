module

public import PottsContinuity.BD12.TwoBlockConnectivity
public import PottsContinuity.PD.FK.Marginal
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder

/-!
# Removing prewired edges preserves actual arc-connection probability

Boundary-internal edges need not be preserved by reflected duality. First
integrate out those edges. Although actual point-to-point paths can change,
the event of some actual path between the two entire wired arcs is unchanged.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance wiredArcRemovalEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Adding or removing sampled states on prewired edges does not change the
actual connection event between two separate, nonempty wired vertex sets. -/
theorem arcsConnectionEvent_union_removed (A B : Set V) (hAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R →
        (twoBlockBoundary A B hAB).partition.r u v)
    (ω : Configuration G) (η : RemovedConfiguration G R) :
    ω ∪ η.val ∈ arcsConnectionEvent G A B ↔ ω ∈ arcsConnectionEvent G A B := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  rw [← twoBlockBoundary_connected_iff A B hAB (ω ∪ η.val) hu hv,
    ← twoBlockBoundary_connected_iff A B hAB ω hu hv,
    componentSetoid_union_removed G (twoBlockBoundary A B hAB) R hR ω η]

end
end PottsContinuity.BD12
