-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxConfigurationExtension.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.FKC.FiniteFK.SlitScreenDualEdgeClassification

@[expose] public section

namespace PottsContinuity.FKC

namespace FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The vertex inclusion of the slit-box graph into the square lattice. -/
def slitBoxGraphHom (n : ℕ) : slitBoxGraph n →g squareLattice where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact (slitBoxGraph_adj_iff n u v).mp huv |>.1

/-- Each actual slit edge, viewed as the same unordered edge of the full lattice. -/
def slitBoxEdgeEmbedding (n : ℕ) :
    (slitBoxGraph n).edgeSet ↪ squareLattice.edgeSet where
  toFun := (slitBoxGraphHom n).mapEdgeSet
  inj' := by
    exact (SimpleGraph.Hom.mapEdgeSet.injective (slitBoxGraphHom n)
      Subtype.val_injective)

@[simp] theorem slitBoxEdgeEmbedding_val (n : ℕ)
    (e : (slitBoxGraph n).edgeSet) :
    (slitBoxEdgeEmbedding n e).val = Sym2.map Subtype.val e.val := rfl

/-- Extend a slit-box configuration to the whole lattice by closing every
lattice edge outside its actual slit-edge image. -/
def slitBoxConfigurationExtension (n : ℕ)
    (A : Configuration (slitBoxGraph n)) : LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.map (slitBoxEdgeEmbedding n))

@[simp] theorem slitBoxConfigurationExtension_at (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (e : (slitBoxGraph n).edgeSet) :
    slitBoxConfigurationExtension n A (slitBoxEdgeEmbedding n e) = decide (e ∈ A) := by
  classical
  simp [slitBoxConfigurationExtension]

@[simp] theorem slitBoxConfigurationExtension_at_true_iff (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (e : (slitBoxGraph n).edgeSet) :
    slitBoxConfigurationExtension n A (slitBoxEdgeEmbedding n e) = true ↔ e ∈ A := by
  rw [slitBoxConfigurationExtension_at]
  simp

end
end FiniteFK
end PottsContinuity.FKC

