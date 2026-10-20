module

public import PottsContinuity.Thm3.Prop4.CensoredClusterReveal
public import PottsContinuity.Thm3.RSW.InducedConfiguration
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Exact induced-complement law for the actual censored-cluster record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G H : SimpleGraph V}
local instance censoredComplementEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Literal surviving vertices of a multiple-seed censored exploration. -/
def censoredSeedComplement (hHG : H ≤ G) (S : Set V) (A : Configuration G) : Set V :=
  (censoredSeedCluster hHG S A)ᶜ

/-- The actual incident-edge reveal deletes precisely the complement of the surviving induced graph. -/
theorem censoredSeedReveal_eq_removed (hHG : H ≤ G) (S : Set V) (A : Configuration G) :
    censoredSeedReveal hHG S A = subgraphRemovedEdges
      ((G.induce (censoredSeedComplement hHG S A)).map
        (RSW.inducedVertexEmbedding (censoredSeedComplement hHG S A))) G := by
  classical
  ext e
  rw [mem_censoredSeedReveal,mem_subgraphRemovedEdges]
  let C := censoredSeedCluster hHG S A
  let f := RSW.inducedVertexEmbedding (censoredSeedComplement hHG S A)
  obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective e.val
  change s(u,v) = e.val at huv
  have hG : G.Adj u v := G.mem_edgeSet.mp (by rw [huv]; exact e.property)
  have hmap : e.val ∈ ((G.induce (censoredSeedComplement hHG S A)).map f).edgeSet ↔
      u ∉ C ∧ v ∉ C := by
    rw [← huv,SimpleGraph.mem_edgeSet,SimpleGraph.map_adj]
    constructor
    · rintro ⟨a,b,_,ha,hb⟩
      have ha' : a.val = u := ha
      have hb' : b.val = v := hb
      exact ⟨ha' ▸ a.property,hb' ▸ b.property⟩
    · rintro ⟨hu,hv⟩
      exact ⟨⟨u,hu⟩,⟨v,hv⟩,hG,rfl,rfl⟩
  have hinc : (∃ z ∈ e.val, z ∈ C) ↔ u ∈ C ∨ v ∈ C := by
    rw [← huv]
    constructor
    · rintro ⟨z,hzE,hzC⟩
      rcases Sym2.mem_iff'.mp hzE with hz | hz
      · exact Or.inl (hz ▸ hzC)
      · exact Or.inr (hz ▸ hzC)
    · rintro (hu | hv)
      · exact ⟨u,Sym2.mem_iff'.mpr (Or.inl rfl),hu⟩
      · exact ⟨v,Sym2.mem_iff'.mpr (Or.inr rfl),hv⟩
  change (∃ z ∈ e.val, z ∈ C) ↔ e.val ∉ ((G.induce (censoredSeedComplement hHG S A)).map f).edgeSet
  rw [hinc,hmap]
  tauto

/-- On each attained record the remaining induced graph has the exact frozen FK law. -/
theorem law_filter_censoredSeedRecord_map_complement (θ : Parameters)
    (ξ : BoundaryCondition V) (hHG : H ≤ G) (S : Set V) (A₀ : Configuration G) :
    ((law G θ ξ).filter (Exploration.revealRecordEvent (censoredSeedReveal hHG S) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (censoredSeedReveal hHG S) (censoredSeedReveal_stable hHG S) A₀]
        exact frozenStateEvent_support θ ξ (censoredSeedReveal hHG S A₀)
          (Exploration.revealRecordConfiguration (censoredSeedReveal hHG S) A₀))).map
      (RSW.inducedConfigurationRestriction (censoredSeedComplement hHG S A₀)) =
    law (G.induce (censoredSeedComplement hHG S A₀)) θ
      (isolatedExtensionPullbackBoundary
        (RSW.inducedVertexEmbedding (censoredSeedComplement hHG S A₀))
        (frozenBoundary ξ (Exploration.revealRecordConfiguration (censoredSeedReveal hHG S) A₀).val)) := by
  let C := censoredSeedComplement hHG S A₀
  let f := RSW.inducedVertexEmbedding C
  let J := (G.induce C).map f
  let R := censoredSeedReveal hHG S A₀
  let K := Exploration.revealRecordConfiguration (censoredSeedReveal hHG S) A₀
  have hR : R = subgraphRemovedEdges J G := censoredSeedReveal_eq_removed hHG S A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges J G) :=
    ⟨K.val,by rw [← hR]; exact K.property⟩
  have hevent : Exploration.revealRecordEvent (censoredSeedReveal hHG S) A₀ =
      frozenStateEvent (subgraphRemovedEdges J G) K' := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent
      (censoredSeedReveal hHG S) (censoredSeedReveal_stable hHG S) A₀]
    ext B
    simp [frozenStateEvent,K',K,R,hR]
  have hfiltered :
      (law G θ ξ).filter (Exploration.revealRecordEvent (censoredSeedReveal hHG S) A₀)
        (by
          rw [Exploration.revealRecordEvent_eq_frozenStateEvent
            (censoredSeedReveal hHG S) (censoredSeedReveal_stable hHG S) A₀]
          exact frozenStateEvent_support θ ξ (censoredSeedReveal hHG S A₀)
            (Exploration.revealRecordConfiguration (censoredSeedReveal hHG S) A₀)) =
      (law G θ ξ).filter (frozenStateEvent (subgraphRemovedEdges J G) K')
        (frozenStateEvent_support θ ξ (subgraphRemovedEdges J G) K') := by
    congr 1
  rw [hfiltered]
  exact law_filter_frozen_map_embeddedRestriction (G.induce C) G f
    (RSW.inducedVertexEmbedding_map_le C) θ ξ K'

end
end PottsContinuity.Thm3.Prop4
