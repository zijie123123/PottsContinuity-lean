module

public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Exact actual connection transport under closed induced extension -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

/-- Closed extension of an induced sample is exactly the embedded actual open graph. -/
theorem inducedExtension_openGraph (C : Set V) (A : Configuration (G.induce C)) :
    openGraph G (RSW.inducedConfigurationExtension C A) =
      (openGraph (G.induce C) A).map (RSW.inducedVertexEmbedding C) := by
  apply SimpleGraph.edgeSet_injective
  rw [openGraph_edgeSet,SimpleGraph.edgeSet_map,openGraph_edgeSet]
  simp only [openEdges,RSW.inducedConfigurationExtension,embeddedConfigurationEmbedding_eq_map,
    Finset.coe_map,Set.image_image]
  rfl

/-- Closing all exterior edges preserves actual connections between sampled vertices. -/
theorem inducedExtension_connection_iff (C : Set V) (A : Configuration (G.induce C))
    (x y : C) :
    ActualConnected G (RSW.inducedConfigurationExtension C A) x.val y.val ↔
      ActualConnected (G.induce C) A x y := by
  change (openGraph G _).Reachable x.val y.val ↔ _
  rw [inducedExtension_openGraph]
  exact reachable_isolatedExtension_apply _ _ x y

variable [Finite V]

omit [Finite V] in
/-- A whole target event transports exactly when the target set is inside the induced domain. -/
theorem inducedExtension_target_iff (C W : Set V) (hWC : W ⊆ C)
    (A : Configuration (G.induce C)) (x : C) :
    RSW.inducedConfigurationExtension C A ∈ targetConnectionEvent x.val W ↔
      A ∈ targetConnectionEvent x (RSW.inducedVertexEmbedding C ⁻¹' W) := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact ⟨⟨y,hWC hy⟩,hy,(inducedExtension_connection_iff C A x ⟨y,hWC hy⟩).mp hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y.val,hy,(inducedExtension_connection_iff C A x y).mpr hxy⟩

omit [Finite V] in
/-- The same exact event identity holds for restriction followed by closed extension. -/
theorem inducedErasure_target_iff (C W : Set V) (hWC : W ⊆ C)
    (A : Configuration G) (x : C) :
    RSW.inducedConfigurationErasure C A ∈ targetConnectionEvent x.val W ↔
      RSW.inducedConfigurationRestriction C A ∈
        targetConnectionEvent x (RSW.inducedVertexEmbedding C ⁻¹' W) :=
  inducedExtension_target_iff C W hWC _ x

end
end PottsContinuity.Thm3.Prop4
