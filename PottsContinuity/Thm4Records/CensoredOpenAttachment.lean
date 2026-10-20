module

public import PottsContinuity.Thm4Records.ClusterFrontier

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK
noncomputable section
section Generic
variable {V : Type*} [Finite V] {G H : SimpleGraph V}

omit [Finite V] in
/-- Both endpoints of a sampled open edge are actually connected. -/
theorem open_edge_endpoints_actualConnected
    (A : Configuration G) (e : G.edgeSet) (he : e ∈ A)
    {u v : V} (hu : u ∈ e.val) (hv : v ∈ e.val) :
    ActualConnected G A u v := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  have hopen : (openGraph G A).Adj a b := by
    rw [openGraph_adj]
    exact ⟨e,he,hab.symm⟩
  rw [← hab] at hu hv
  rcases Sym2.mem_iff'.mp hu with rfl | rfl <;>
    rcases Sym2.mem_iff'.mp hv with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hopen.reachable
  · exact hopen.reachable.symm
  · exact SimpleGraph.Reachable.refl _

/-- A recorded open censored edge has both endpoints in the explored cluster. -/
theorem censoredSeedReveal_open_edge_endpoint_reached
    (hHG : H ≤ G) (S : Set V) (A : Configuration G) (e : H.edgeSet)
    (he : Thm3.Prop4.censoredEdgeInclusion hHG e ∈ A)
    (hr : Thm3.Prop4.censoredEdgeInclusion hHG e ∈
      Thm3.Prop4.censoredSeedReveal hHG S A)
    (u : V) (hu : u ∈ e.val) :
    u ∈ Thm3.Prop4.censoredSeedCluster hHG S A := by
  obtain ⟨v,hv,s,hs,hsv⟩ := (Thm3.Prop4.mem_censoredSeedReveal hHG S A _).mp hr
  refine ⟨s,hs,hsv.trans ?_⟩
  exact open_edge_endpoints_actualConnected (Thm3.Prop4.censoredConfiguration hHG A) e
    ((Thm3.Prop4.mem_censoredConfiguration hHG A e).mpr he) hv hu

end Generic
end
end PottsContinuity.Thm4Records
