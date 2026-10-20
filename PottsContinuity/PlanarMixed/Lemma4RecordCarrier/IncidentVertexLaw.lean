module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ResidualPrimalWindows
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK
noncomputable section

/-- Retain exactly vertices incident to at least one graph edge. -/
def incidentVertexSet {V : Type*} (G : SimpleGraph V) : Set V :=
  {u | ∃ v, G.Adj u v}

def incidentVertexEmbedding {V : Type*} (G : SimpleGraph V) : incidentVertexSet G ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem incidentVertexGraph_map {V : Type*} (G : SimpleGraph V) :
    (G.induce (incidentVertexSet G)).map (incidentVertexEmbedding G) = G := by
  ext x y
  constructor
  · intro h
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    exact huv
  · intro h
    apply (SimpleGraph.map_adj _ _ _ _).mpr
    exact ⟨⟨x,y,h⟩,⟨y,x,h.symm⟩,h,rfl,rfl⟩

/-- Restriction to incident vertices removes no bonds or sampled states. -/
def incidentVertexConfigurationRead {V : Type*} [Finite V] (G : SimpleGraph V) :
    Configuration G → Configuration (G.induce (incidentVertexSet G)) :=
  embeddedConfigurationRestriction _ G (incidentVertexEmbedding G) (incidentVertexGraph_map G).le

theorem embeddedRestriction_law_of_graph_map_eq {U V : Type*} [Finite U] [Finite V]
    (H : SimpleGraph U) (G : SimpleGraph V) (f : U ↪ V)
    (hgraph : H.map f=G) (θ : Parameters) (ξ : BoundaryCondition V) :
    (law G θ ξ).map (embeddedConfigurationRestriction H G f hgraph.le) =
      law H θ (isolatedExtensionPullbackBoundary f ξ) := by
  subst G
  rw [← law_isolatedExtension_map_boundary_pullback H f θ ξ,PMF.map_comp]
  have hinv : embeddedConfigurationRestriction H (H.map f) f (by rfl) ∘
      isolatedExtensionConfigurationEquiv H f = id := by
    funext A
    ext e
    change e ∈ embeddedConfigurationRestriction H (H.map f) f _ (isolatedExtensionConfigurationEquiv H f A) ↔ e ∈ A
    rw [mem_embeddedConfigurationRestriction]
    rw [show embeddedEdgeEmbedding H (H.map f) f _ e = isolatedExtensionEdgeEquiv H f e from rfl]
    simp [isolatedExtensionConfigurationEquiv]
  rw [hinv,PMF.map_id]

theorem incidentVertexConfigurationRead_law {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V) :
    (law G θ ξ).map (incidentVertexConfigurationRead G) =
      law (G.induce (incidentVertexSet G)) θ
        (isolatedExtensionPullbackBoundary (incidentVertexEmbedding G) ξ) :=
  embeddedRestriction_law_of_graph_map_eq _ G _ (incidentVertexGraph_map G) θ ξ

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
