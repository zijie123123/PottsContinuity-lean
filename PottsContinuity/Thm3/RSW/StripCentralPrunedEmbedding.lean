module

public import PottsContinuity.Thm3.RSW.StripTopRowEdgeRead
public import PottsContinuity.Thm3.RSW.StripWindowEdgeRead
public import PottsContinuity.Thm3.RSW.StripCentralRead
public import PottsContinuity.DualityExt.PositiveDualSubgraphEdgeState

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

/-- The unchanged physical central rectangle embeds in every sufficiently
wide original source host. -/
def stripCentralPrimalHostEmbedding (n k M : ℕ) (hM : k*n+1 ≤ M) :
    RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) ↪
      RectangleVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) :=
  (Function.Embedding.refl (ℤ×ℤ)).subtypeMap (by
    intro v hv
    have hv := (mem_latticeRectangle _ _ _ _).mp hv
    rw [mem_latticeRectangle]
    change (-(M:ℤ) ≤ v.1 ∧ v.1 ≤ -(M:ℤ)+((2*M:ℕ):ℤ)) ∧
      -(n:ℤ) ≤ v.2 ∧ v.2 ≤ -(n:ℤ)+((4*n:ℕ):ℤ)
    push_cast at hv ⊢
    simp only [neg_mul,mul_assoc] at hv
    have hkn : (k:ℤ)*n+1 ≤ M := by exact_mod_cast hM
    constructor <;> constructor <;> omega)

/-- Every central source bond survives deletion of the prewired top row. -/
theorem stripCentralPrimalHost_map_le_pruned (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M) :
    (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map
      (stripCentralPrimalHostEmbedding n k M hM) ≤
      (stripRectangleWithoutTopGraph n M).map (Function.Embedding.refl _) := by
  classical
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  rw [SimpleGraph.map_adj]
  refine ⟨_,_,?_,rfl,rfl⟩
  rw [stripRectangleWithoutTopGraph,edgeRestriction,SimpleGraph.deleteEdges_adj]
  refine ⟨hxy,?_⟩
  intro he
  let e : (rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).edgeSet :=
    ⟨s(stripCentralPrimalHostEmbedding n k M hM x,stripCentralPrimalHostEmbedding n k M hM y),(rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).mem_edgeSet.mpr hxy⟩
  have he' := (coe_mem_openEdges_iff _ _ e).mp he
  have ht := (mem_stripRectangleTopRowState_iff n M _).mp he'
  have hx := ht (stripCentralPrimalHostEmbedding n k M hM x) (by simp [e])
  have hv := (mem_latticeRectangle _ _ _ _).mp x.property
  change x.val.2=3*(n:ℤ) at hx
  push_cast at hv
  omega

/-- The actual global retained dual edge crossed by each local primal bond. -/
def stripCentralRetainedDualEdge (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (e : (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet) :
    (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)).edgeSet :=
  rectangleSubgraphDualEdgeEmbedding (stripRectangleWithoutTop_map_le n M)
    (embeddedEdgeEmbedding _ _ (stripCentralPrimalHostEmbedding n k M hM)
      (stripCentralPrimalHost_map_le_pruned n k M hn hM) e)

/-- Physical identity from the central rectangle into the original source window. -/
def stripCentralPrimalWindowEmbedding (n k M : ℕ) (hM : k*n+1 ≤ M) :
    RectangleVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) ↪
      (stripWindow n M : Set (ℤ×ℤ)) :=
  (stripCentralPrimalHostEmbedding n k M hM).trans (stripWindowRectangleIso n M).symm.toEquiv.toEmbedding

/-- The literal original central bonds embed in the original finite sample. -/
theorem stripCentralPrimalWindow_map_le (n k M : ℕ) (hM : k*n+1 ≤ M) :
    (rectangleGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map
      (stripCentralPrimalWindowEmbedding n k M hM) ≤
      squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hxy

/-- The infinite-strip central read of a finite source sample is precisely
its original-bond restriction to the central rectangle. -/
theorem stripCentralRectangleConfiguration_windowRead (n k M : ℕ) (hM : k*n+1 ≤ M)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) :
    stripCentralRectangleConfiguration n k (stripWindowOriginalRead n M C) =
      embeddedConfigurationRestriction _ _ (stripCentralPrimalWindowEmbedding n k M hM)
        (stripCentralPrimalWindow_map_le n k M hM) C := by
  classical
  ext e
  rw [stripCentralRectangleConfiguration,mem_boolConfigurationEquiv,mem_embeddedConfigurationRestriction]
  rw [stripWindowOriginalRead_edge n M C
    (embeddedEdgeEmbedding _ _ (stripCentralPrimalWindowEmbedding n k M hM)
      (stripCentralPrimalWindow_map_le n k M hM) e) _ (by
        simp only [embeddedEdgeEmbedding_coe,Function.Embedding.sym2Map_apply,Sym2.map_map]
        rfl)]
  simp [boolConfigurationEquiv]

end
end PottsContinuity.RSW
