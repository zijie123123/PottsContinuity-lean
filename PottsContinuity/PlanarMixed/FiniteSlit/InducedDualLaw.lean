module

public import PottsContinuity.PlanarMixed.FiniteSlit.DualSampledCarrier
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw

/-! The finite active FK law maps to the actual induced reflected dual law.
This transfers conditioning exactly; the remaining geometric boundary
calculation is exposed in inducedDualBoundary, without replacing its relation. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitInducedDualLawEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The exact boundary induced by the fixed dual exterior state. -/
def inducedDualBoundary (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) : BoundaryCondition (Vertex M x) :=
  isolatedExtensionPullbackBoundary (cellEmbedding M x hM)
    (frozenBoundary (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M)
      (dualExteriorState M x y).val)

/-- Read precisely the reflected sampled edges inside the full dual host. -/
def dualHostRestriction (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) :=
  embeddedConfigurationRestriction (dualGraph M x y)
    (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (cellEmbedding M x hM)
    (dualGraph_map_le_rectangleDual M x y hM)

theorem dualRemovedEdges_eq_mapped_complement (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    subgraphRemovedEdges ((dualGraph M x y).map (cellEmbedding M x hM))
      (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) = dualRemovedEdges M x y := by
  ext e
  rw [mem_subgraphRemovedEdges,← dualSampledGraph_eq_map M x y hM hy hyM]
  rw [dualSampledGraph,edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff,e.property,true_and,coe_mem_openEdges_iff,not_not]

/-- The fixed dual rectangle restricts to its full induced-boundary FK law. -/
theorem dual_law_of_conditioned_rectangle (θ : Parameters)
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    ((law (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) θ
      (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M)).filter
      (frozenStateEvent _ (dualExteriorState M x y))
      (frozenStateEvent_support θ _ _ (dualExteriorState M x y))).map
      (dualHostRestriction M x y hM) = law (dualGraph M x y) θ (inducedDualBoundary M x y hM) := by
  let K : RemovedConfiguration (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M)
      (subgraphRemovedEdges ((dualGraph M x y).map (cellEmbedding M x hM))
        (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M)) :=
    ⟨(dualExteriorState M x y).val,by
      rw [dualRemovedEdges_eq_mapped_complement M x y hM hy hyM]
      exact (dualExteriorState M x y).property⟩
  have hevent : frozenStateEvent _ K = frozenStateEvent _ (dualExteriorState M x y) := by
    ext C
    change C ∩ _ = _ ↔ C ∩ _ = _
    dsimp only [K]
    rw [dualRemovedEdges_eq_mapped_complement M x y hM hy hyM]
  have h := law_filter_frozen_map_embeddedRestriction _ _ (cellEmbedding M x hM)
    (dualGraph_map_le_rectangleDual M x y hM) θ
    (rectangleDualBoundaryCondition (x-(M : ℤ),0) (2*M-1) M) K
  simpa only [hevent,K,dualHostRestriction,inducedDualBoundary] using h

/-- Reading the host dual sample commutes exactly with the finite complement. -/
theorem hostRestriction_dual_transport (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (C : Configuration (rectangleGraph (x-(M : ℤ),0) (2*M-1) M)) :
    dualHostRestriction M x y hM
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M C) =
    activeDualConfigurationEquiv M x y hM hy hyM (hostRestriction M x y C) := by
  ext t
  obtain ⟨a,rfl⟩ := (activeCrossingEdgeEquiv M x y hM hy hyM).surjective t
  rw [activeDualConfigurationEquiv_mem]
  change _ ∈ embeddedConfigurationRestriction _ _ _ _ _ ↔
    _ ∉ subgraphConfigurationRestriction _ C
  rw [mem_embeddedConfigurationRestriction,mem_subgraphConfigurationRestriction]
  change dualHostEdgeEmbedding M x y hM _ ∈ _ ↔ _
  rw [← dualHostEdgeEmbedding_eq_crossing M x y hM hy hyM]
  exact rectangleDualEdgeEquiv_mem_dualConfiguration C _

/-- Exact finite active duality with the computed induced boundary, for every
independent interior FK parameter. No boundary identification is assumed. -/
theorem active_law_map_dual_eq_induced (θ : Parameters)
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (law (activeGraph M x y) θ (boundary M x y hM hy hyM)).map
      (activeDualConfigurationEquiv M x y hM hy hyM) =
    law (dualGraph M x y) (dualParameters θ) (inducedDualBoundary M x y hM) := by
  have h := congrArg (fun p => p.map (dualHostRestriction M x y hM))
    (conditioned_rectangle_duality θ M x y)
  rw [PMF.map_comp,dual_law_of_conditioned_rectangle (dualParameters θ) M x y hM hy hyM] at h
  have hc : dualHostRestriction M x y hM ∘
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M) =
      (activeDualConfigurationEquiv M x y hM hy hyM) ∘ hostRestriction M x y :=
    funext (hostRestriction_dual_transport M x y hM hy hyM)
  rw [hc,← PMF.map_comp,active_law_of_conditioned_free_rectangle θ M x y hM hy hyM] at h
  exact h

end
end PottsContinuity.PlanarMixed.FiniteSlit
