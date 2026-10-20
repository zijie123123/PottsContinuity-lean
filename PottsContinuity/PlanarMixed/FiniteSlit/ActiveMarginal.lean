module

public import PottsContinuity.PlanarMixed.FiniteSlit.InducedDualLaw
public import PottsContinuity.PD.FK.Marginal

/-! Exact marginal and canonical complementary map of the original finite
source law. Only already prewired internal arc states are integrated out. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section
local instance finiteSlitActiveMarginalEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Read exactly the original non-internal sampled source bonds. -/
def activeRestriction (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    Configuration (activeGraph M x y) :=
  (edgeRestrictionConfigurationEquiv (graph M x y) (internalEdges M x y)).symm
    (configurationSplitEquiv (graph M x y) (internalEdges M x y) C).1

/-- Restriction preserves every genuine active edge state. -/
theorem activeRestriction_mem (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y))
    (e : (activeGraph M x y).edgeSet) :
    e ∈ activeRestriction M x y C ↔
      edgeRestrictionEdgeEmbedding (graph M x y) (internalEdges M x y) e ∈ C := by
  let R := internalEdges M x y
  let E := edgeRestrictionConfigurationEquiv (graph M x y) R
  have h := congrArg Subtype.val (E.apply_symm_apply
    (configurationSplitEquiv (graph M x y) R C).1)
  rw [edgeRestrictionConfigurationEquiv_val] at h
  change (activeRestriction M x y C).map (edgeRestrictionEdgeEmbedding (graph M x y) R) = C \ R at h
  have hn : edgeRestrictionEdgeEmbedding (graph M x y) R e ∉ R :=
    (edgeRestrictionEdgeEquiv (graph M x y) R e).property
  constructor
  · intro he
    have hm := Finset.mem_map_of_mem (edgeRestrictionEdgeEmbedding (graph M x y) R) he
    rw [h] at hm
    exact (Finset.mem_sdiff.mp hm).1
  · intro he
    have hm : edgeRestrictionEdgeEmbedding (graph M x y) R e ∈
        (activeRestriction M x y C).map (edgeRestrictionEdgeEmbedding (graph M x y) R) := by
      rw [h]
      exact Finset.mem_sdiff.mpr ⟨he,hn⟩
    exact (Finset.mem_map' _).mp hm

/-- Integrating all internal source arc states gives the ordinary active FK law. -/
theorem activeRestriction_law (θ : Parameters) (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (law (graph M x y) θ (boundary M x y hM hy hyM)).map (activeRestriction M x y) =
      law (activeGraph M x y) θ (boundary M x y hM hy hyM) := by
  let E := edgeRestrictionConfigurationEquiv (graph M x y) (internalEdges M x y)
  have hr := law_map_remove (graph M x y) θ (boundary M x y hM hy hyM) (internalEdges M x y)
    (internalEdges_prewired M x y hM hy hyM)
  have h := congrArg (fun p => p.map E.symm) hr
  rw [PMF.map_comp,← law_edgeRestriction_map,PMF.map_comp] at h
  have he : E.symm ∘ E = id := funext E.symm_apply_apply
  rw [he,PMF.map_id] at h
  exact h

/-- Normalized target labels retain the original active inverse bond. -/
theorem dualPreimageBond_normalized (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (b : {b : LatticeBond // ActiveBond M x y b}) :
    dualPreimageBond M x y (normalizedDualEdgeEquiv M x y hM hy hyM b) = b.val := by
  have he : dualEdgeEmbedding M x y (normalizedDualEdgeEquiv M x y hM hy hyM b) =
      latticeBondEdge (slitReflectedBond x b.val) := Subtype.ext rfl
  unfold dualPreimageBond
  rw [he]
  have hb : wholePlaneBondEdgeEquiv.symm (latticeBondEdge (slitReflectedBond x b.val)) =
      slitReflectedBond x b.val := wholePlaneBondEdgeEquiv.symm_apply_apply _
  rw [hb,slitReflectedBondInv_apply]

/-- The canonical inverse edge agrees with the literal original active edge. -/
theorem sourcePreimageEdge_normalized (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (b : {b : LatticeBond // ActiveBond M x y b}) :
    sourcePreimageEdge M x y (normalizedDualEdgeEquiv M x y hM hy hyM b) =
      edgeRestrictionEdgeEmbedding (graph M x y) (internalEdges M x y)
        (normalizedActiveEdgeEquiv M x y b) := by
  apply (edgeEmbedding M x y).injective
  rw [sourcePreimageEdge_embedding,dualPreimageBond_normalized]
  exact Subtype.ext rfl

/-- The canonical full-source complement factors through its exact active marginal. -/
theorem dualConfiguration_factor (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) (C : Configuration (graph M x y)) :
    dualConfiguration M x y C =
      activeDualConfigurationEquiv M x y hM hy hyM (activeRestriction M x y C) := by
  ext t
  obtain ⟨b,rfl⟩ := (normalizedDualEdgeEquiv M x y hM hy hyM).surjective t
  have he : normalizedDualEdgeEquiv M x y hM hy hyM b =
      activeCrossingEdgeEquiv M x y hM hy hyM (normalizedActiveEdgeEquiv M x y b) := by
    simp only [activeCrossingEdgeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [mem_dualConfiguration,sourcePreimageEdge_normalized,he,
    activeDualConfigurationEquiv_mem,activeRestriction_mem]

/-- The original full finite source law maps to the exact induced dual FK law.
All internal arc-state noise has been integrated out without an extra premise. -/
theorem law_map_dual_eq_induced (θ : Parameters) (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (law (graph M x y) θ (boundary M x y hM hy hyM)).map (dualConfiguration M x y) =
      law (dualGraph M x y) (PD.Duality.dualParameters θ) (inducedDualBoundary M x y hM) := by
  have hf : dualConfiguration M x y =
      (activeDualConfigurationEquiv M x y hM hy hyM) ∘ activeRestriction M x y :=
    funext (dualConfiguration_factor M x y hM hy hyM)
  rw [hf,← PMF.map_comp,activeRestriction_law θ M x y hM hy hyM]
  exact active_law_map_dual_eq_induced θ M x y hM hy hyM

end
end PottsContinuity.PlanarMixed.FiniteSlit
