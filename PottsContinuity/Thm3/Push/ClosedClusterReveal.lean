module

public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

local instance closedRevealEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

local instance closedRevealEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance closedRevealAuxEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- Closed primal states read as open auxiliary states through an edge
bijection. For the true rectangle dual this is the literal dual configuration. -/
def auxiliaryClosedConfiguration (e : G.edgeSet ≃ H.edgeSet) (A : Configuration G) :
    Configuration H := by
  classical
  exact (Finset.univ \ A).map e.toEmbedding

omit [Finite W] in
@[simp] theorem mem_auxiliaryClosedConfiguration (e : G.edgeSet ≃ H.edgeSet)
    (A : Configuration G) (f : H.edgeSet) :
    f ∈ auxiliaryClosedConfiguration e A ↔ e.symm f ∉ A := by
  classical
  simp [auxiliaryClosedConfiguration, Finset.mem_map_equiv]

/-- Reveal original primal states at every auxiliary edge incident to a
closed-dual cluster reached from the fixed seed set. Pure exploration uses
FKC's proved combinatorics, independently of its cluster-weight restriction. -/
def closedClusterReveal (e : G.edgeSet ≃ H.edgeSet) (S : Finset W)
    (A : Configuration G) : Configuration G :=
  (FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A)).map
    e.symm.toEmbedding

@[simp] theorem mem_closedClusterReveal (e : G.edgeSet ≃ H.edgeSet) (S : Finset W)
    (A : Configuration G) (f : G.edgeSet) :
    f ∈ closedClusterReveal e S A ↔
      e f ∈ FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A) := by
  classical
  simp [closedClusterReveal, Finset.mem_map_equiv]

/-- Agreement on the revealed primal states gives agreement on all the
incident auxiliary closed-edge states, including closed cluster boundaries. -/
theorem auxiliaryClosedConfiguration_agree_on_reveal
    (e : G.edgeSet ≃ H.edgeSet) (S : Finset W) (A B : Configuration G)
    (hagree : B ∩ closedClusterReveal e S A = A ∩ closedClusterReveal e S A) :
    auxiliaryClosedConfiguration e B ∩
        FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A) =
      auxiliaryClosedConfiguration e A ∩
        FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A) := by
  classical
  ext f
  by_cases hf : f ∈ FKC.FiniteFK.actualMultiClusterReveal H S (auxiliaryClosedConfiguration e A)
  · have hp : e.symm f ∈ closedClusterReveal e S A := by simpa using hf
    have hstate := Finset.ext_iff.mp hagree (e.symm f)
    simp only [Finset.mem_inter, hp, and_true] at hstate
    simp only [Finset.mem_inter, mem_auxiliaryClosedConfiguration, hf, and_true, hstate]
  · simp only [Finset.mem_inter, hf, and_false]

/-- This concrete dual-cluster reveal is a stopping set on the ORIGINAL
primal configuration carrier; no selector-locality hypothesis is assumed. -/
theorem closedClusterReveal_stable (e : G.edgeSet ≃ H.edgeSet) (S : Finset W)
    (A B : Configuration G)
    (hagree : B ∩ closedClusterReveal e S A = A ∩ closedClusterReveal e S A) :
    closedClusterReveal e S B = closedClusterReveal e S A := by
  unfold closedClusterReveal
  congr 1
  exact FKC.FiniteFK.actualMultiClusterReveal_consistent S _ _
    (auxiliaryClosedConfiguration_agree_on_reveal e S A B hagree)

/-- The actual reached auxiliary vertex set is determined by the recorded
primal states, as required for later geometric frontier extraction. -/
theorem closedCluster_reached_iff_of_reveal_agreement
    (e : G.edgeSet ≃ H.edgeSet) (S : Finset W) (A B : Configuration G)
    (hagree : B ∩ closedClusterReveal e S A = A ∩ closedClusterReveal e S A) (v : W) :
    (∃ s ∈ S, ActualConnected H (auxiliaryClosedConfiguration e B) s v) ↔
      ∃ s ∈ S, ActualConnected H (auxiliaryClosedConfiguration e A) s v := by
  exact FKC.FiniteFK.actualMultiClusterConnected_iff_of_reveal_agreement S _ _
    (auxiliaryClosedConfiguration_agree_on_reveal e S A B hagree) v

end
end PottsContinuity.Push
