module

public import PottsContinuity.Thm3.RSW.StripAsymmetricReadMeasures
public import PottsContinuity.Thm3.RSW.StripWindowEdgeRead
public import PottsContinuity.Thm3.RSW.StripReflectedCentralDualRead

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section
local instance stripReflectedFiniteReadEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Every reflected central dual vertex lies in the actual centered finite
source window as soon as that window contains the extra dual left column. -/
def stripReflectedCentralWindowEmbedding (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M) :
    RectangleDualVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) ↪
      (stripWindow n M : Set (ℤ×ℤ)) :=
  ((stripReflectedCentralDualEmbedding n k hn).trans
    (⟨Subtype.val,Subtype.val_injective⟩ : stripVertices n ↪ (ℤ×ℤ))).codRestrict _ (by
    intro v
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    have hkn : (k:ℤ)*n+1 ≤ M := by exact_mod_cast hM
    change (v.val.1,2*(n:ℤ)-1-v.val.2) ∈ stripWindow n M
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    push_cast at hv
    simp only [neg_mul,mul_assoc] at hv
    constructor <;> constructor <;> omega)

/-- Each reflected central dual bond is an actual original window bond. -/
theorem stripReflectedCentralWindow_map_le (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M) :
    (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map
      (stripReflectedCentralWindowEmbedding n k M hn hM) ≤
      squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact stripReflectedCentralDual_map_le n k hn
    ((SimpleGraph.map_adj _ _ _ _).mpr ⟨x,y,hxy,rfl,rfl⟩)

/-- The same literal reflected read in the full asymmetric source rectangle. -/
def stripReflectedCentralAsymmetricEmbedding (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M) :=
  (stripReflectedCentralWindowEmbedding n k M hn hM).trans (stripWindowAsymmetricEmbedding n M)

/-- No reflected local bond is altered by inclusion into the asymmetric host. -/
theorem stripReflectedCentralAsymmetric_map_le (n k M : ℕ) (hn : 1 ≤ n) (hM : k*n+1 ≤ M) :
    (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map
      (stripReflectedCentralAsymmetricEmbedding n k M hn hM) ≤
      rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact stripReflectedCentralWindow_map_le n k M hn hM
    ((SimpleGraph.map_adj _ _ _ _).mpr ⟨x,y,hxy,rfl,rfl⟩)

/-- The reflected infinite-strip read of an asymmetric finite sample equals
restriction to precisely its original reflected local bonds. -/
theorem stripReflectedCentralDualConfiguration_asymmetricRead (n k M : ℕ)
    (hn : 1 ≤ n) (hM : k*n+1 ≤ M)
    (C : Configuration (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n))) :
    stripReflectedCentralDualConfiguration n k hn (stripAsymmetricCenteredRead n M C) =
      embeddedConfigurationRestriction _ _ (stripReflectedCentralAsymmetricEmbedding n k M hn hM)
        (stripReflectedCentralAsymmetric_map_le n k M hn hM) C := by
  classical
  ext e
  rw [stripReflectedCentralDualConfiguration,mem_boolConfigurationEquiv,mem_embeddedConfigurationRestriction]
  change stripWindowOriginalRead n M
    (embeddedConfigurationRestriction _ _ (stripWindowAsymmetricEmbedding n M)
      (stripWindowAsymmetric_map_le n M) C) _ = true ↔ _
  rw [stripWindowOriginalRead_edge n M _
    (embeddedEdgeEmbedding _ _ (stripReflectedCentralWindowEmbedding n k M hn hM)
      (stripReflectedCentralWindow_map_le n k M hn hM) e) _ (by
        simp only [embeddedEdgeEmbedding_coe,Function.Embedding.sym2Map_apply,Sym2.map_map]
        rfl)]
  simp only [boolConfigurationEquiv,Equiv.coe_fn_symm_mk,decide_eq_true_eq,
    mem_embeddedConfigurationRestriction]
  have heq : embeddedEdgeEmbedding _ _ (stripWindowAsymmetricEmbedding n M)
      (stripWindowAsymmetric_map_le n M)
      (embeddedEdgeEmbedding _ _ (stripReflectedCentralWindowEmbedding n k M hn hM)
        (stripReflectedCentralWindow_map_le n k M hn hM) e) =
    embeddedEdgeEmbedding _ _ (stripReflectedCentralAsymmetricEmbedding n k M hn hM)
      (stripReflectedCentralAsymmetric_map_le n k M hn hM) e := by
    apply Subtype.ext
    simp only [embeddedEdgeEmbedding_coe,Function.Embedding.sym2Map_apply,Sym2.map_map]
    rfl
  rw [heq]

end
end PottsContinuity.RSW
