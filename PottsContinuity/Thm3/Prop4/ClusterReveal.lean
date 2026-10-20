module

public import PottsContinuity.FKC.FiniteFK.ClusterExploration
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Actual cluster exploration at independent FK parameters

The reveal and its stability are the parameter-independent proved FKC
construction. The conditional law uses the PD all-q finite stopping-set DMP;
no restriction q<4 or assumption on the revealed cluster is introduced.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance clusterRevealEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance clusterRevealEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance clusterRevealRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- Reveal every edge incident to the actual seed cluster, including its closed boundary. -/
def clusterReveal (u : V) (A : Configuration G) : Configuration G :=
  FKC.FiniteFK.actualClusterReveal G u A

theorem clusterReveal_mem_iff (u : V) (A : Configuration G) (e : G.edgeSet) :
    e ∈ clusterReveal G u A ↔ ∃ v : V, v ∈ e.val ∧ ActualConnected G A u v :=
  FKC.FiniteFK.actualClusterReveal_mem_iff G u A e

/-- The actual cluster is determined by the complete revealed edge states. -/
theorem clusterConnected_iff_of_reveal_agreement (u : V) (A B : Configuration G)
    (hagree : B ∩ clusterReveal G u A = A ∩ clusterReveal G u A) (v : V) :
    ActualConnected G B u v ↔ ActualConnected G A u v :=
  FKC.FiniteFK.actualConnected_iff_of_reveal_agreement G u A B hagree v

/-- The literal incident-edge cluster reveal is a stopping set. -/
theorem clusterReveal_stable (u : V) (A B : Configuration G)
    (hagree : B ∩ clusterReveal G u A = A ∩ clusterReveal G u A) :
    clusterReveal G u B = clusterReveal G u A :=
  FKC.FiniteFK.actualClusterReveal_consistent G u A B hagree

end

end PottsContinuity.Thm3.Prop4
