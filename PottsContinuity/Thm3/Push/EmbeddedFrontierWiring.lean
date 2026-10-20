module

public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import PottsContinuity.Thm3.Push.EmbeddedReveal
public import PottsContinuity.Thm3.Push.FilledFrontierFrozenBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance embeddedFrontierEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An actual open connection maps to an actual open connection on the
embedded original bonds, without using any boundary identifications. -/
theorem actualConnected_embeddedConfiguration {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : Configuration G) {u v : V} (huv : ActualConnected G A u v) :
    ActualConnected H (embeddedConfigurationEmbedding G H f hGH A) (f u) (f v) := by
  change ActualConnected H
    (subgraphConfigurationEmbedding hGH (isolatedExtensionConfigurationEquiv G f A)) (f u) (f v)
  rw [ActualConnected,openGraph_subgraphConfigurationEmbedding]
  exact (actualConnected_isolatedExtension G f A u v).mpr huv

/-- In an outer exploration record the actual frontier bonds are observed
OPEN. This is a state-level inclusion, including the closed states of the
filled reveal; no conditional probability assumption is used. -/
theorem embedded_filledFrontier_subset_open_record {V : Type*} [Finite V]
    (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G) :
    embeddedConfigurationEmbedding _ _ f hRG
      (rectangleFilledTopFrontier a w h (embeddedConfigurationRestriction _ _ f hRG A)) ⊆
    A ∩ embeddedReveal _ _ f hRG (rectangleFilledTopReveal a w h) A := by
  rw [embeddedConfigurationEmbedding_eq_map]
  intro g hg
  obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hg
  have hfr := rectangleFilledTopFrontier_subset_open_and_revealed a w h
    (embeddedConfigurationRestriction _ _ f hRG A) he
  exact Finset.mem_inter.mpr
    ⟨(mem_embeddedConfigurationRestriction _ _ _ _ _ e).mp (Finset.mem_inter.mp hfr).1,
      (mem_embeddedReveal_at_edge _ _ _ _ _ A e).mpr
        (rectangleTopReveal_subset_filled a w h _ (Finset.mem_inter.mp hfr).2)⟩

/-- The frozen OUTER boundary identifies all actual frontier vertices with
its physical side class. The only boundary premise identifies the original
physical sides; all required frontier connections and observed-open states
are supplied by proved exploration geometry. -/
theorem embedded_frontier_wiring_le_actual_frozen {V : Type*} [Finite V]
    (a : LatticeVertex) (w h : ℕ) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v)) :
    (BoundaryCondition.wired
      (filledFrontierWiredVertices a w h (embeddedConfigurationRestriction _ _ f hRG A))).partition ≤
    (isolatedExtensionPullbackBoundary f
      (frozenBoundary ξ
        (A ∩ embeddedReveal _ _ f hRG (rectangleFilledTopReveal a w h) A))).partition := by
  let K := A ∩ embeddedReveal _ _ f hRG (rectangleFilledTopReveal a w h) A
  have hK := embedded_filledFrontier_subset_open_record a w h G f hRG A
  intro u v huv
  change (frozenBoundary ξ K).partition.r (f u) (f v)
  rcases huv with rfl | ⟨hu,hv⟩
  · exact (frozenBoundary ξ K).partition.refl _
  · obtain ⟨u',hu',huu'⟩ := filledFrontierWiredVertices_connects_to_side a w h _ hA u hu
    obtain ⟨v',hv',hvv'⟩ := filledFrontierWiredVertices_connects_to_side a w h _ hA v hv
    have hU := actualConnected_component G ξ K (actualConnected_mono hK
      (actualConnected_embeddedConfiguration _ _ f hRG _ huu'))
    have hV := actualConnected_component G ξ K (actualConnected_mono hK
      (actualConnected_embeddedConfiguration _ _ f hRG _ hvv'))
    have hS := boundary_component G ξ K (hsides u' v' hu' hv')
    exact (componentSetoid G ξ K).trans
      ((componentSetoid G ξ K).trans hU hS) ((componentSetoid G ξ K).symm hV)

end
end PottsContinuity.Push
