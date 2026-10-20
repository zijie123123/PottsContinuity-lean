module

public import PottsContinuity.Thm3.Prop4.ClusterReveal
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# A stable exploration of multiple clusters in a fixed censored graph

Clusters are computed using a fixed subgraph H of the ambient graph G, while
ALL ambient edges incident to those clusters are revealed. In particular this
permits stopping at a prescribed wired arc without ignoring the states of edges
leading into the arc. No FK boundary comparison is assumed or concluded here.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section
variable {V : Type*} [Finite V] {G H : SimpleGraph V}
local instance censoredEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance censoredEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance censoredSubEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance censoredSubEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- The identical original edge, viewed in the ambient graph. -/
def censoredEdgeInclusion (hHG : H ≤ G) (e : H.edgeSet) : G.edgeSet :=
  ⟨e.val,SimpleGraph.edgeSet_mono hHG e.property⟩

/-- Read the original states on precisely the fixed censored subgraph. -/
def censoredConfiguration (hHG : H ≤ G) (A : Configuration G) : Configuration H :=
  Finset.univ.filter fun e => censoredEdgeInclusion hHG e ∈ A

@[simp] theorem mem_censoredConfiguration (hHG : H ≤ G) (A : Configuration G)
    (e : H.edgeSet) : e ∈ censoredConfiguration hHG A ↔ censoredEdgeInclusion hHG e ∈ A := by
  simp [censoredConfiguration]

/-- The union of the genuine censored open clusters attached to the specified seeds. -/
def censoredSeedCluster (hHG : H ≤ G) (S : Set V) (A : Configuration G) : Set V :=
  {v | ∃ s ∈ S, ActualConnected H (censoredConfiguration hHG A) s v}

/-- Reveal ambient incident edges, including edges absent from the censored graph. -/
def censoredSeedReveal (hHG : H ≤ G) (S : Set V) (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e => ∃ v ∈ e.val, v ∈ censoredSeedCluster hHG S A

@[simp] theorem mem_censoredSeedReveal (hHG : H ≤ G) (S : Set V)
    (A : Configuration G) (e : G.edgeSet) :
    e ∈ censoredSeedReveal hHG S A ↔ ∃ v ∈ e.val, v ∈ censoredSeedCluster hHG S A := by
  classical
  simp [censoredSeedReveal]

/-- Agreement on the ambient reveal includes the whole ordinary reveal of each censored seed. -/
theorem censored_seed_reveal_agreement (hHG : H ≤ G) (S : Set V)
    (A B : Configuration G)
    (hagree : B ∩ censoredSeedReveal hHG S A = A ∩ censoredSeedReveal hHG S A)
    {s : V} (hs : s ∈ S) :
    censoredConfiguration hHG B ∩ clusterReveal H s (censoredConfiguration hHG A) =
      censoredConfiguration hHG A ∩ clusterReveal H s (censoredConfiguration hHG A) := by
  ext e
  by_cases he : e ∈ clusterReveal H s (censoredConfiguration hHG A)
  · obtain ⟨v,hve,hsv⟩ := (clusterReveal_mem_iff H s _ e).mp he
    have heR : censoredEdgeInclusion hHG e ∈ censoredSeedReveal hHG S A := by
      apply (mem_censoredSeedReveal hHG S A _).mpr
      exact ⟨v,hve,s,hs,hsv⟩
    have hstate := Finset.ext_iff.mp hagree (censoredEdgeInclusion hHG e)
    simpa only [Finset.mem_inter, mem_censoredConfiguration, heR, he, and_true] using hstate
  · simp only [Finset.mem_inter,he,and_false]

/-- The entire censored seed cluster is determined by the attained ambient record. -/
theorem censoredSeedCluster_eq_of_agreement (hHG : H ≤ G) (S : Set V)
    (A B : Configuration G)
    (hagree : B ∩ censoredSeedReveal hHG S A = A ∩ censoredSeedReveal hHG S A) :
    censoredSeedCluster hHG S B = censoredSeedCluster hHG S A := by
  ext v
  constructor
  · rintro ⟨s,hs,hsv⟩
    exact ⟨s,hs,(clusterConnected_iff_of_reveal_agreement H s _ _
      (censored_seed_reveal_agreement hHG S A B hagree hs) v).mp hsv⟩
  · rintro ⟨s,hs,hsv⟩
    exact ⟨s,hs,(clusterConnected_iff_of_reveal_agreement H s _ _
      (censored_seed_reveal_agreement hHG S A B hagree hs) v).mpr hsv⟩

/-- Multiple censored clusters give a genuine stopping set on the ambient edges. -/
theorem censoredSeedReveal_stable (hHG : H ≤ G) (S : Set V) (A B : Configuration G)
    (hagree : B ∩ censoredSeedReveal hHG S A = A ∩ censoredSeedReveal hHG S A) :
    censoredSeedReveal hHG S B = censoredSeedReveal hHG S A := by
  ext e
  rw [mem_censoredSeedReveal,mem_censoredSeedReveal,
    censoredSeedCluster_eq_of_agreement hHG S A B hagree]

end
end PottsContinuity.Thm3.Prop4
