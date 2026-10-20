module

public import PottsContinuity.Thm3.Prop4.ClusterFreeLaw
public import PottsContinuity.Thm3.RSW.InducedConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Actual connection witnesses outside an attained seed-cluster record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Connection from a specified root to some vertex of the literal target set. -/
def targetConnectionEvent (u : V) (T : Set V) : Set (Configuration G) :=
  {A | ∃ w ∈ T, ActualConnected G A u w}

omit [Finite V] in
theorem targetConnectionEvent_upper (u : V) (T : Set V) :
    IsUpperSet (targetConnectionEvent (G := G) u T) := by
  rintro A B hAB ⟨w,hw,hconn⟩
  exact ⟨w,hw,actualConnected_mono hAB hconn⟩

/-- Every root connection is determined by its complete actual-cluster record. -/
theorem targetConnectionEvent_clusterRecord_iff (u : V) (T : Set V) (A₀ A : Configuration G)
    (hrecord : A ∈ Exploration.revealRecordEvent (clusterReveal G u) A₀) :
    A ∈ targetConnectionEvent u T ↔ A₀ ∈ targetConnectionEvent u T := by
  constructor
  · rintro ⟨w,hw,hconn⟩
    exact ⟨w,hw,(clusterConnected_iff_of_reveal_agreement G u A₀ A hrecord.2 w).mp hconn⟩
  · rintro ⟨w,hw,hconn⟩
    exact ⟨w,hw,(clusterConnected_iff_of_reveal_agreement G u A₀ A hrecord.2 w).mpr hconn⟩

/-- The whole actual cluster of a root outside the revealed cluster survives
restriction to the same attained complement, including its witnessing paths. -/
theorem clusterRecord_connection_survives_erasure (u v : V) (A₀ A : Configuration G)
    (hrecord : A ∈ Exploration.revealRecordEvent (clusterReveal G u) A₀)
    (hv : v ∈ clusterComplement u A₀) {w : V} (hvw : ActualConnected G A v w) :
    ActualConnected G (RSW.inducedConfigurationErasure (clusterComplement u A₀) A) v w := by
  have hav : ¬ ActualConnected G A u v := by
    intro h
    exact hv ((clusterConnected_iff_of_reveal_agreement G u A₀ A hrecord.2 v).mp h)
  have havoid (x : V) (hvx : ActualConnected G A v x) : x ∈ clusterComplement u A₀ := by
    intro hux
    have huxA := (clusterConnected_iff_of_reveal_agreement G u A₀ A hrecord.2 x).mpr hux
    exact hav (huxA.trans hvx.symm)
  change (openGraph G A).Reachable v w at hvw
  rw [SimpleGraph.reachable_iff_reflTransGen] at hvw
  change (openGraph G (RSW.inducedConfigurationErasure (clusterComplement u A₀) A)).Reachable v w
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hvw with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y hprefix hxy ih =>
    have hvx : ActualConnected G A v x := by
      change (openGraph G A).Reachable v x
      rw [SimpleGraph.reachable_iff_reflTransGen]
      exact hprefix
    have hvy : ActualConnected G A v y := hvx.trans hxy.reachable
    obtain ⟨e,he,heval⟩ := (openGraph_adj G A x y).mp hxy
    have hsurvive : e ∈ RSW.inducedConfigurationErasure (clusterComplement u A₀) A := by
      apply (RSW.mem_inducedConfigurationErasure _ A e).mpr
      refine ⟨he,?_⟩
      intro z hz
      rw [heval] at hz
      rcases Sym2.mem_iff'.mp hz with h | h
      · rw [h]
        exact havoid x hvx
      · rw [h]
        exact havoid y hvy
    have hnew : (openGraph G (RSW.inducedConfigurationErasure (clusterComplement u A₀) A)).Adj x y :=
      (openGraph_adj G _ x y).mpr ⟨e,hsurvive,heval⟩
    exact ih.tail hnew

/-- A second root's target event survives the same record erasure when the two clusters differ. -/
theorem targetConnection_survives_clusterRecord (u v : V) (T : Set V) (A₀ A : Configuration G)
    (hrecord : A ∈ Exploration.revealRecordEvent (clusterReveal G u) A₀)
    (hv : v ∈ clusterComplement u A₀) (hA : A ∈ targetConnectionEvent v T) :
    RSW.inducedConfigurationErasure (clusterComplement u A₀) A ∈ targetConnectionEvent v T := by
  obtain ⟨w,hw,hvw⟩ := hA
  exact ⟨w,hw,clusterRecord_connection_survives_erasure u v A₀ A hrecord hv hvw⟩

end
end PottsContinuity.Thm3.Prop4
