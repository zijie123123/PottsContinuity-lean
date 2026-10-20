module

public import PottsContinuity.Thm3.RSW.StripCentralPrunedRead
public import PottsContinuity.Thm3.RSW.StripCentralDualEdgeLabel
public import PottsContinuity.Thm3.RSW.StripReflectedFiniteRead

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section
local instance stripPrunedReflectionEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The retained global dual label is exactly the physical reflection of
the original asymmetric sample's reflected local bond. -/
theorem stripCentralRetainedDualEdge_reflected (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (d : (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet) :
    subgraphEdgeEmbedding (stripPrunedDual_le_reflectedAsymmetric n M)
      (stripCentralRetainedDualEdge n k M hn hM
        ((rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n)).symm d)) =
    isolatedExtensionEdgeEquiv
      (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n))
      (stripReflectedAsymmetricEmbedding n M)
      (embeddedEdgeEmbedding _ _ (stripReflectedCentralAsymmetricEmbedding n k M hn hM)
        (stripReflectedCentralAsymmetric_map_le n k M hn hM) d) := by
  apply Subtype.ext
  apply Sym2.map.injective (f := fun z : RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) => z.val)
    Subtype.val_injective
  change Sym2.map Subtype.val
    (stripCentralRetainedDualEdge n k M hn hM
      ((rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n)).symm d)).val = _
  rw [stripCentralRetainedDualEdge_physical_pair,Equiv.apply_symm_apply]
  change Sym2.map Subtype.val d.val =
    Sym2.map Subtype.val (Sym2.map (stripReflectedAsymmetricEmbedding n M)
      (embeddedEdgeEmbedding _ _ (stripReflectedCentralAsymmetricEmbedding n k M hn hM)
        (stripReflectedCentralAsymmetric_map_le n k M hn hM) d).val)
  simp only [embeddedEdgeEmbedding_coe,Function.Embedding.sym2Map_apply,Sym2.map_map]
  congr 1
  funext z
  apply Prod.ext
  · rfl
  · change z.val.2=2*(n:ℤ)-1-(2*(n:ℤ)-1-z.val.2)
    omega

/-- The actual retained global dual read of the asymmetric sample agrees
pointwise with the reflected original central read. -/
theorem stripCentralPrunedDualRead_reflected (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (C : Configuration (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n))) :
    stripCentralPrunedDualRead n k M hn hM (stripAsymmetricPrunedDualRead n M C) =
      stripReflectedCentralDualConfiguration n k hn (stripAsymmetricCenteredRead n M C) := by
  classical
  rw [stripReflectedCentralDualConfiguration_asymmetricRead n k M hn hM C]
  ext d
  rw [stripCentralPrunedDualRead,mem_boolConfigurationEquiv,decide_eq_true_eq,
    stripAsymmetricPrunedDualRead,mem_subgraphConfigurationRestriction,
    stripCentralRetainedDualEdge_reflected,mem_embeddedConfigurationRestriction]
  change isolatedExtensionEdgeEquiv _ _ _ ∈
    C.map (isolatedExtensionEdgeEquiv _ _).toEmbedding ↔ _
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

end
end PottsContinuity.RSW
