module

public import PottsContinuity.Thm4Plane.ScreenCapDomainPlaneEvent
public import PottsContinuity.FKC.FiniteFK.CrossingComponentRemoval
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Infinite

noncomputable section

local instance screenCapResidualAmbientEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _
local instance screenCapResidualAmbientEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

/-- The inclusion of the cap-domain vertex carrier into the slit-box carrier. -/
def screenCapDomainVertexEmbeddingToSlitBox (m : ℕ)
    (D : Set (SlitBoxVertex (16 * m))) :
    {v : SlitBoxVertex (16 * m) // v ∈ D} ↪ SlitBoxVertex (16 * m) where
  toFun v := v.val
  inj' := Subtype.val_injective

local instance screenCapResidualMappedEdgeFintype (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    Fintype ((screenCapEdgeDeletedDomainGraph m R D).map
      (screenCapDomainVertexEmbeddingToSlitBox m D)).edgeSet := Fintype.ofFinite _

/-- The edge-deleted cap domain is a subgraph of the original slit box. -/
theorem screenCapEdgeDeletedDomainGraph_map_to_slitBox (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    (screenCapEdgeDeletedDomainGraph m R D).map
      (screenCapDomainVertexEmbeddingToSlitBox m D) ≤ slitBoxGraph (16 * m) := by
  intro u v huv
  obtain ⟨u', v', hadj, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (screenCapDomainVertexEmbeddingToSlitBox m D)
      (screenCapEdgeDeletedDomainGraph m R D) u v).mp huv
  change ((edgeRestriction (slitBoxGraph (16 * m)) R).induce D).Adj u' v' at hadj
  exact edgeRestriction_le (slitBoxGraph (16 * m)) R
    (SimpleGraph.induce_adj.mp hadj)

/-- Reveal exactly the edges outside the embedded edge-deleted cap domain. -/
noncomputable def screenCapComplementReveal (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    PottsContinuity.Exploration.RevealMap
      (G := slitBoxGraph (16 * m)) :=
  fun _ => PottsContinuity.PD.FK.subgraphRemovedEdges
    ((screenCapEdgeDeletedDomainGraph m R D).map
      (screenCapDomainVertexEmbeddingToSlitBox m D))
    (slitBoxGraph (16 * m))

/-- Restrict a source configuration first to the graph with `R` deleted and
then to the induced domain `D`. -/
noncomputable def screenCapResidualConfiguration (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m)))
    (A : Configuration (slitBoxGraph (16 * m))) :
    Configuration (screenCapEdgeDeletedDomainGraph m R D) := by
  let G := slitBoxGraph (16 * m)
  let H := edgeRestriction G R
  let K := H.induce D
  let f : D ↪ SlitBoxVertex (16 * m) := ⟨Subtype.val, Subtype.val_injective⟩
  let hHG : H ≤ G := edgeRestriction_le G R
  let hKH : K.map f ≤ H := by
    intro u v huv
    rcases (SimpleGraph.map_adj f K u v).mp huv with
      ⟨u', v', hK, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mp hK
  exact embeddedConfigurationRestriction K H f hKH
    (subgraphConfigurationRestriction hHG A)

/-- An open source edge whose two endpoints are in the cap survives both
configuration restrictions when the deleted set avoids cap-internal edges. -/
theorem screenCapResidualConfiguration_adj_of_source_adj_of_no_internal_removal
    (m : ℕ) (R : Configuration (slitBoxGraph (16 * m)))
    (hR : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e)
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D)
    (A : Configuration (slitBoxGraph (16 * m)))
    {u v : SlitBoxVertex (16 * m)}
    (hu : u ∈ screenTargetCap m) (hv : v ∈ screenTargetCap m)
    (hOpen : (openGraph (slitBoxGraph (16 * m)) A).Adj u v) :
    (openGraph (screenCapEdgeDeletedDomainGraph m R D)
      (screenCapResidualConfiguration m R D A)).Adj
      ⟨u, hcap hu⟩ ⟨v, hcap hv⟩ := by
  classical
  let G := slitBoxGraph (16 * m)
  let H := edgeRestriction G R
  let K := H.induce D
  let f : D ↪ SlitBoxVertex (16 * m) := ⟨Subtype.val, Subtype.val_injective⟩
  have hHG : H ≤ G := edgeRestriction_le G R
  have hKH : K.map f ≤ H := by
    intro x y hxy
    rcases (SimpleGraph.map_adj f K x y).mp hxy with
      ⟨x', y', hK, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mp hK
  rcases (openGraph_adj_iff_openBond G A u v).mp hOpen with ⟨hG, heA⟩
  let eG : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr hG⟩
  have hInternal : screenTargetCapInternalEdge m eG :=
    ⟨⟨u, hu⟩, ⟨v, hv⟩, rfl⟩
  have heNotR : eG ∉ R := by
    intro heR
    exact hR eG heR hInternal
  have hH : H.Adj u v := by
    apply H.mem_edgeSet.mpr
    change s(u, v) ∈ H.edgeSet
    rw [edgeRestriction_edgeSet]
    refine ⟨G.mem_edgeSet.mpr hG, ?_⟩
    intro hopen
    exact heNotR ((coe_mem_openEdges_iff G R eG).mp hopen)
  have hK : K.Adj ⟨u, hcap hu⟩ ⟨v, hcap hv⟩ :=
    SimpleGraph.induce_adj.mpr hH
  let eH : H.edgeSet := ⟨s(u, v), H.mem_edgeSet.mpr hH⟩
  let eK : K.edgeSet :=
    ⟨s(⟨u, hcap hu⟩, ⟨v, hcap hv⟩), K.mem_edgeSet.mpr hK⟩
  have heH : eH ∈ subgraphConfigurationRestriction
      hHG A := by
    apply (mem_subgraphConfigurationRestriction
      hHG A eH).2
    have heq : subgraphEdgeEmbedding (edgeRestriction_le G R) eH = eG := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact heA
  have heK : eK ∈ screenCapResidualConfiguration m R D A := by
    change eK ∈ embeddedConfigurationRestriction K H f hKH
      (subgraphConfigurationRestriction hHG A)
    apply (mem_embeddedConfigurationRestriction K H f hKH
      (subgraphConfigurationRestriction hHG A) eK).2
    have heq : embeddedEdgeEmbedding K H f hKH eK = eH := by
      apply Subtype.ext
      simp [embeddedEdgeEmbedding_coe, f, eK, eH]
    rw [heq]
    exact heH
  have hBond : ∃ h : K.Adj ⟨u, hcap hu⟩ ⟨v, hcap hv⟩,
      (⟨s(⟨u, hcap hu⟩, ⟨v, hcap hv⟩), K.mem_edgeSet.mpr h⟩ : K.edgeSet) ∈
        screenCapResidualConfiguration m R D A := by
    exact ⟨hK, heK⟩
  exact (openGraph_adj_iff_openBond K
    (screenCapResidualConfiguration m R D A)
    ⟨u, hcap hu⟩ ⟨v, hcap hv⟩).mpr hBond

/-- The source screen event yields its residual cap event for the canonical
restricted configuration, provided the deleted bonds avoid the cap. -/
theorem generalEScreenEvent_residualCapBoundaryConnection_of_no_internal_removal
    (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (hR : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e)
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m)) :
    screenCapResidualConfiguration m R D A ∈
      screenCapBoundaryConnectionEvent m R D hcap := by
  apply generalEScreenEvent_residualCapBoundaryConnection_of_adjacencyAgreement
    m R D hcap A hE (screenCapResidualConfiguration m R D A)
  intro u v hu hv hOpen
  exact screenCapResidualConfiguration_adj_of_source_adj_of_no_internal_removal
    m R hR D hcap A hu hv hOpen

/-- The canonical edge-deleted component supplies an induced domain containing
the whole cap, so the same residual path transfer applies without a separate
choice of `D`. -/
theorem generalEScreenEvent_component_residualCapBoundaryConnection
    (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (slitBoxGraph (16 * m)))
    (hR : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m)) :
    screenCapResidualConfiguration m R
        (screenTargetCapEdgeDeletedComponent m R) A ∈
      screenCapBoundaryConnectionEvent m R
        (screenTargetCapEdgeDeletedComponent m R)
        (screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal
          m hm R hR) := by
  exact generalEScreenEvent_residualCapBoundaryConnection_of_no_internal_removal
    m R hR (screenTargetCapEdgeDeletedComponent m R)
    (screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal
      m hm R hR) A hE

end
end PottsContinuity.Thm4Plane
