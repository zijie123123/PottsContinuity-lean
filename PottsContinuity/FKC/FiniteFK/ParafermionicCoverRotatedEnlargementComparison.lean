-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRotatedEnlargementComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EmbeddedFreeConnectionComparison
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedBoxLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open MeasureTheory

noncomputable section

/-- Embed the original finite cover box into the common enlarged box by an
actual iterate of the sheet-corrected quarter-turn. -/
def parafermionicCoverQuarterTurnEnlargementEmbedding (n : ℕ) (j : Fin 4) :
    ParafermionicCoverBoxVertex n ↪ ParafermionicCoverBoxVertex (n + 1) where
  toFun v := ⟨parafermionicCoverQuarterTurnIsoIterate j.val v.val,
    by
      rw [parafermionicCoverQuarterTurnIsoIterate_apply]
      exact parafermionicCoverQuarterTurn_iterates_mem_box_succ n v.val v.property j⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact (parafermionicCoverQuarterTurnIsoIterate j.val).injective
      (congrArg Subtype.val h)

@[simp] theorem parafermionicCoverQuarterTurnEnlargementEmbedding_val
    (n : ℕ) (j : Fin 4) (v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverQuarterTurnEnlargementEmbedding n j v).val =
      (parafermionicCoverQuarterTurn^[j.val]) v.val := by
  simp [parafermionicCoverQuarterTurnEnlargementEmbedding]

theorem parafermionicCoverQuarterTurnEnlargementEmbedding_map_le
    (n : ℕ) (j : Fin 4) :
    (parafermionicCoverBoxGraph n).map
      (parafermionicCoverQuarterTurnEnlargementEmbedding n j) ≤
      parafermionicCoverBoxGraph (n + 1) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro x y hxy
  change (parafermionicCoverBoxGraph (n + 1)).Adj
    (parafermionicCoverQuarterTurnEnlargementEmbedding n j x)
    (parafermionicCoverQuarterTurnEnlargementEmbedding n j y)
  rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj]
  change parafermionicCoverGraph.Adj x.val y.val at hxy
  exact (parafermionicCoverQuarterTurnIsoIterate j.val).map_rel_iff.mpr hxy

theorem parafermionicCoverQuarterTurn_enlargement_connection_probability_le
    (n : ℕ) (j : Fin 4) (q : ClusterWeight)
    (x y : ParafermionicCoverBoxVertex n) :
    (measure (parafermionicCoverBoxGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n)))
      (connectivityEvent (parafermionicCoverBoxGraph n) x y)).toReal ≤
    (measure (parafermionicCoverBoxGraph (n + 1)) q
      (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
      (connectivityEvent (parafermionicCoverBoxGraph (n + 1))
        (parafermionicCoverQuarterTurnEnlargementEmbedding n j x)
        (parafermionicCoverQuarterTurnEnlargementEmbedding n j y))).toReal := by
  exact embedded_free_connection_probability_le
    (parafermionicCoverQuarterTurnEnlargementEmbedding n j)
    (parafermionicCoverQuarterTurnEnlargementEmbedding_map_le n j) q x y

end

end PottsContinuity.FKC.FiniteFK
