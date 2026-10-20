module

public import PottsContinuity.Thm3.RSW.StripCentralPrunedEmbedding

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section
local instance stripCentralPrunedReadEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Read actual retained global dual bonds with the local dual labels. -/
def stripCentralPrunedDualRead (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (C : Configuration (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M))) :
    Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)) :=
  boolConfigurationEquiv _ (fun d => decide
    (stripCentralRetainedDualEdge n k M hn hM
      ((rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n)).symm d) ∈ C))

/-- The local retained dual read is exactly the complement of the same
original central bonds in the finite source sample. -/
theorem stripCentralPrunedDualRead_source (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) :
    stripCentralPrunedDualRead n k M hn hM (stripWindowPrunedDualConfiguration n M C) =
      stripCentralDualConfiguration n k (stripWindowOriginalRead n M C) := by
  classical
  ext d
  obtain ⟨e,rfl⟩ := (rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n)).surjective d
  rw [stripCentralPrunedDualRead,mem_boolConfigurationEquiv,Equiv.symm_apply_apply,decide_eq_true_eq]
  have hl : rectangleDualEdgeEquiv (-(k:ℤ)*n,0) (2*k*n) (2*n) e ∈
      stripCentralDualConfiguration n k (stripWindowOriginalRead n M C) ↔
      e ∉ stripCentralRectangleConfiguration n k (stripWindowOriginalRead n M C) := by
    exact mem_rectanglePrimalDualConfigurationEquiv _ _ _ _
      (rectanglePrimalDualEdgeEquiv _ _ _ e)
  rw [hl,stripCentralRectangleConfiguration_windowRead n k M hM C]
  change _ ↔ ¬ e ∈ embeddedConfigurationRestriction _ _ _ _ C
  rw [mem_embeddedConfigurationRestriction]
  let J := stripRectangleWithoutTopGraph n M
  let f := Function.Embedding.refl (RectangleVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n))
  let g := embeddedEdgeEmbedding _ _ (stripCentralPrimalHostEmbedding n k M hM)
    (stripCentralPrimalHost_map_le_pruned n k M hn hM) e
  let p := (isolatedExtensionEdgeEquiv J f).symm g
  change rectangleSubgraphDualEdgeEmbedding (stripRectangleWithoutTop_map_le n M) g ∈
      rectangleSubgraphDualConfigurationEquiv (stripRectangleWithoutTop_map_le n M)
        (isolatedExtensionConfigurationEquiv J f
          (subgraphConfigurationRestriction (stripRectangleWithoutTop_le n M)
            (configurationIso (stripWindowRectangleIso n M) C))) ↔ _
  rw [rectangleSubgraphDualConfigurationEquiv_edgeState]
  apply not_congr
  have hg : g=isolatedExtensionEdgeEquiv J f p :=
    ((isolatedExtensionEdgeEquiv J f).apply_symm_apply g).symm
  rw [hg]
  change isolatedExtensionEdgeEquiv J f p ∈
      (subgraphConfigurationRestriction (stripRectangleWithoutTop_le n M)
        (configurationIso (stripWindowRectangleIso n M) C)).map
          (isolatedExtensionEdgeEquiv J f).toEmbedding ↔ _
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
  rw [mem_subgraphConfigurationRestriction]
  let eorig := embeddedEdgeEmbedding _ _ (stripCentralPrimalWindowEmbedding n k M hM)
    (stripCentralPrimalWindow_map_le n k M hM) e
  have heq : subgraphEdgeEmbedding (stripRectangleWithoutTop_le n M) p =
      configurationIsoEdgeEquiv (stripWindowRectangleIso n M) eorig := by
    apply Subtype.ext
    have hp := congrArg Subtype.val hg
    change g.val=Sym2.map f p.val at hp
    change p.val= _
    calc
      p.val=g.val := by simpa [f] using hp.symm
      _ = _ := by
        simp only [g,eorig,embeddedEdgeEmbedding_coe,
          Function.Embedding.sym2Map_apply,configurationIsoEdgeEquiv]
        simp only [SimpleGraph.Iso.mapEdgeSet_apply,SimpleGraph.Hom.mapEdgeSet]
        change Sym2.map (stripCentralPrimalHostEmbedding n k M hM) e.val =
          Sym2.map (stripWindowRectangleIso n M)
            (Sym2.map (stripCentralPrimalWindowEmbedding n k M hM) e.val)
        rw [Sym2.map_map]
        rfl
  rw [heq]
  change configurationIsoEdgeEquiv (stripWindowRectangleIso n M) eorig ∈
      C.map (configurationIsoEdgeEquiv (stripWindowRectangleIso n M)).toEmbedding ↔ _
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
  rfl

end
end PottsContinuity.RSW
