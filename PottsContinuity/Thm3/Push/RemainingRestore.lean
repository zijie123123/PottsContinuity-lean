module

public import PottsContinuity.Thm3.Push.ActiveFrontierComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance remainingRestoreEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Put the observed open states back onto a configuration of the actual
unexamined graph. This is exactly the inverse of the existing FK split. -/
def restoreRemainingConfiguration {V : Type*} (G : SimpleGraph V) (R : Configuration G)
    (K : RemovedConfiguration G R) (C : Configuration (edgeRestriction G R)) : Configuration G :=
  (configurationSplitEquiv G R).symm (edgeRestrictionConfigurationEquiv G R C,K)

/-- Restoring leaves the recorded original states exactly fixed. -/
theorem restoreRemainingConfiguration_inter {V : Type*} (G : SimpleGraph V)
    (R : Configuration G) (K : RemovedConfiguration G R)
    (C : Configuration (edgeRestriction G R)) :
    restoreRemainingConfiguration G R K C ∩ R = K.val := by
  change ((edgeRestrictionConfigurationEquiv G R C).val ∪ K.val) ∩ R = K.val
  rw [Finset.union_inter_distrib_right,
    Finset.disjoint_iff_inter_eq_empty.mp (edgeRestrictionConfigurationEquiv G R C).property,
    Finset.empty_union,Finset.inter_eq_left.mpr K.property]

/-- The restored original states on active bonds are exactly those of the
actual unexamined graph. Recorded-open edges never alter an active bond. -/
theorem active_restriction_restoreRemainingConfiguration {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G) (K : RemovedConfiguration G R)
    (C : Configuration (edgeRestriction G R)) :
    embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G R) (restoreRemainingConfiguration G R K C) =
    embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le_edgeRestriction G R) C := by
  classical
  ext e
  rw [mem_embeddedConfigurationRestriction,mem_embeddedConfigurationRestriction]
  let g := embeddedEdgeEmbedding _ _ (Function.Embedding.subtype _)
    (activeUnexaminedGraph_map_le_edgeRestriction G R) e
  let f := embeddedEdgeEmbedding _ _ (Function.Embedding.subtype _)
    (activeUnexaminedGraph_map_le G R) e
  have hgf : edgeRestrictionEdgeEmbedding G R g = f := by
    apply Subtype.ext
    rfl
  have hfR : f ∉ R := by
    have hnot := (edgeRestrictionEdgeEquiv G R g).property
    change edgeRestrictionEdgeEmbedding G R g ∉ R at hnot
    simpa only [hgf] using hnot
  have hfK : f ∉ K.val := fun hmem => hfR (K.property hmem)
  change f ∈ (edgeRestrictionConfigurationEquiv G R C).val ∪ K.val ↔ g ∈ C
  rw [Finset.mem_union,or_iff_left hfK,edgeRestrictionConfigurationEquiv_val,← hgf]
  exact Finset.mem_map' _

end
end PottsContinuity.Push
