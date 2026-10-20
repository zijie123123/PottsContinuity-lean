module

public import PottsContinuity.Thm4.CoverConfiguration
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConfigurationExtension
public import PottsContinuity.FKC.FiniteFK.Graph

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section

/-- Both libraries use the same literal cover vertices and seam; their lattice
adjacency definitions agree by the frozen coordinate characterization. -/
theorem fkc_coverGraph_eq : parafermionicCoverGraph =
    PottsContinuity.FKC.parafermionicCoverGraph := by
  ext u v
  change (PottsContinuity.squareLattice.Adj u.1 v.1 ∧ _) ↔
    (PottsContinuity.FKC.squareLattice.Adj u.1 v.1 ∧ _)
  rw [frozen_squareLattice_adj_iff, PottsContinuity.FKC.squareLattice_adj_iff]
  rfl

theorem fkc_ambientGraph_eq (n : ℕ) : ParafermionicAmbientGraph n =
    PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n := by
  unfold ParafermionicAmbientGraph parafermionicCoverBoxGraph
    PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph
    PottsContinuity.FKC.parafermionicCoverBoxGraph
  rw [fkc_coverGraph_eq]
  rfl

/-- Identity on the actual unordered endpoints, with adjacency transported. -/
def fkcEdgeEquiv (n : ℕ) : (ParafermionicAmbientGraph n).edgeSet ≃
    (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n).edgeSet where
  toFun e := ⟨e.1, by rw [← fkc_ambientGraph_eq]; exact e.2⟩
  invFun e := ⟨e.1, by rw [fkc_ambientGraph_eq]; exact e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transfer the complete actual open-edge set along the identity endpoint map. -/
def fkcConfiguration (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) :
    PottsContinuity.FKC.FiniteFK.Configuration
      (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) :=
  A.map (fkcEdgeEquiv n).toEmbedding

@[simp] theorem fkcEdge_mem_configuration (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    fkcEdgeEquiv n e ∈ fkcConfiguration n A ↔ e ∈ A := by
  simp [fkcConfiguration]

/-- Identity on whole-cover edges, preserving their unordered endpoints. -/
def fkcWholeEdgeEquiv : parafermionicCoverGraph.edgeSet ≃
    PottsContinuity.FKC.parafermionicCoverGraph.edgeSet where
  toFun e := ⟨e.1, by rw [← fkc_coverGraph_eq]; exact e.2⟩
  invFun e := ⟨e.1, by rw [fkc_coverGraph_eq]; exact e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fkc_configurationExtension (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtension n
        (fkcConfiguration n A) =
      (parafermionicCoverConfigurationExtension n A).map fkcWholeEdgeEquiv.toEmbedding := by
  unfold PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtension
    fkcConfiguration parafermionicCoverConfigurationExtension
  rw [Finset.map_map, Finset.map_map]
  congr 1

theorem fkc_configurationExtensionState (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (e : parafermionicCoverGraph.edgeSet) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState n
        (fkcConfiguration n A) (fkcWholeEdgeEquiv e) =
      parafermionicCoverConfigurationExtensionState n A e := by
  simp [PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState,
    parafermionicCoverConfigurationExtensionState, fkc_configurationExtension]

/-- Actual open graphs agree on all vertices, including isolated vertices. -/
theorem fkc_openGraph_eq (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) :
    PottsContinuity.FKC.FiniteFK.openGraph
      (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n) (fkcConfiguration n A) =
      openGraph (ParafermionicAmbientGraph n) A := by
  unfold PottsContinuity.FKC.FiniteFK.openGraph openGraph
    PottsContinuity.FKC.FiniteFK.openEdges openEdges fkcConfiguration
  simp only [Finset.coe_map, Set.image_image]
  rfl

theorem fkc_actualConnected_iff (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicAmbientVertex n) :
    PottsContinuity.FKC.FiniteFK.ActualConnected
        (PottsContinuity.FKC.FiniteFK.ParafermionicAmbientGraph n)
        (fkcConfiguration n A) u v ↔ ActualConnected (ParafermionicAmbientGraph n) A u v := by
  unfold PottsContinuity.FKC.FiniteFK.ActualConnected ActualConnected
  rw [fkc_openGraph_eq]
  rfl

end
end PottsContinuity.Thm4
