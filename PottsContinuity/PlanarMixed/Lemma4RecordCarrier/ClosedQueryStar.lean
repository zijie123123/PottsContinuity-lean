module

public import PottsContinuity.Thm3.Push.ClosedClusterFrontier
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Push
noncomputable section

/-- A queried open auxiliary edge has both endpoints in the explored cluster. -/
theorem closedClusterReveal_closed_edge_endpoints_reached
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G.edgeSet ≃ H.edgeSet) (S : Finset W) (A : Configuration G)
    (d : G.edgeSet) (hd : d ∈ closedClusterReveal e S A) (hclosed : d ∉ A)
    (v : W) (hv : v ∈ (e d).val) : v ∈ closedClusterReached e S A := by
  classical
  have he : e d ∈ auxiliaryClosedConfiguration e A := by
    rw [mem_auxiliaryClosedConfiguration,Equiv.symm_apply_apply]
    exact hclosed
  have hr : e d ∈ FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A) :=
    (mem_closedClusterReveal e S A d).mp hd
  exact FKC.FiniteFK.actualMultiClusterRecord_endpoint_connected S
    (auxiliaryClosedConfiguration e A) (by simpa only [FKC.FiniteFK.revealRecordConfiguration,Finset.mem_inter] using And.intro he hr) hv

/-- Every auxiliary edge at a queried open endpoint is queried as well.
Thus a recorded open cluster edge cannot attach to a native active vertex. -/
theorem closedClusterReveal_closed_edge_incident_query
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G.edgeSet ≃ H.edgeSet) (S : Finset W) (A : Configuration G)
    (d : G.edgeSet) (hd : d ∈ closedClusterReveal e S A) (hclosed : d ∉ A)
    (v : W) (hv : v ∈ (e d).val)
    (b : G.edgeSet) (hb : v ∈ (e b).val) : b ∈ closedClusterReveal e S A := by
  apply (mem_closedClusterReveal_iff_endpoint e S A b).mpr
  exact ⟨v,hb,closedClusterReveal_closed_edge_endpoints_reached e S A d hd hclosed v hv⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
