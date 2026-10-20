module

public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance recordedWalkEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- A recorded open walk gives both original endpoint connections to each
visited trace vertex in every sample agreeing with that record. -/
theorem actual_connections_of_recorded_walk {V : Type*} (G : SimpleGraph V)
    (R B C : Configuration G) (hC : C ∩ R = B) {u v z : V}
    (p : (openGraph G B).Walk u v) (hz : z ∈ p.support) :
    ActualConnected G C u z ∧ ActualConnected G C v z := by
  classical
  have hBC : B ⊆ C := by rw [← hC]; exact Finset.inter_subset_left
  have hup : (openGraph G B).Reachable u z := ⟨p.takeUntil z hz⟩
  have hvp : (openGraph G B).Reachable v z :=
    ⟨p.reverse.takeUntil z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)⟩
  exact ⟨hup.mono (openGraph_mono hBC),hvp.mono (openGraph_mono hBC)⟩

end
end PottsContinuity.Thm3.Prop4
