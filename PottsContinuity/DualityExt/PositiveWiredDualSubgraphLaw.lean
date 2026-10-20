module

public import PottsContinuity.DualityExt.PositiveEndpointDualSubgraphLaw
public import PottsContinuity.DualityExt.PositiveGraphRelabeling
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Wired laws from a free law on the dual subgraph

Applying the proved rectangle free-subgraph duality to a rectangle containing
the source dual graph gives a free-to-wired law on its double dual. This file
composes that result with graph relabeling and states the exact boundary
partition identity needed to read the double dual as the source graph.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {K : SimpleGraph (RectangleVertex a w h)}

/-- The wired law on the active double dual is the pushforward of the free law
on a rectangular dual-side subgraph, provided the induced boundary partition
is exactly the desired one. This is the probability-algebra part of the
symmetric wired-to-free reduction; the embedding and partition equality are
separate discrete geometry obligations.
-/
theorem positive_wired_dual_subgraph_law_of_partition_eq
    (hK : K ≤ rectangleGraph a w h)
    {W : Type*} [Finite W]
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃ W)
    (ξ : BoundaryCondition W)
    (hξ : (positiveBoundaryTransport e
      (isolatedExtensionPullbackBoundary
        (positiveActiveInclusion (rectangleSubgraphDualGraph hK))
        (frozenBoundary (rectangleDualBoundaryCondition a w h)
          (rectangleSubgraphRemovedDualEdges hK)))).partition = ξ.partition) :
    (positiveFKLaw
        ((positiveActiveGraph (rectangleSubgraphDualGraph hK)).map e.toEmbedding)
        q p hq hp hp1 ξ).map
      (((rectangleSubgraphDualConfigurationEquiv hK).trans
        (positiveActiveConfigurationEquiv (rectangleSubgraphDualGraph hK)).symm).trans
        (isolatedExtensionConfigurationEquiv
          (positiveActiveGraph (rectangleSubgraphDualGraph hK)) e.toEmbedding)).symm =
      positiveFKLaw K q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
        (BoundaryCondition.free ∅) := by
  let J := rectangleSubgraphDualGraph hK
  let A := positiveActiveGraph J
  let η := frozenBoundary (rectangleDualBoundaryCondition a w h)
    (rectangleSubgraphRemovedDualEdges hK)
  let ηA := isolatedExtensionPullbackBoundary (positiveActiveInclusion J) η
  let d := (rectangleSubgraphDualConfigurationEquiv hK).trans
    (positiveActiveConfigurationEquiv J).symm
  let f := isolatedExtensionConfigurationEquiv A e.toEmbedding
  let E := d.trans f
  let pDual := dualParameter q p
  have hpDual : 0 < pDual := dualParameter_pos hq hp hp1
  have hpDual1 : pDual < 1 := dualParameter_lt_one hq hp hp1
  have hfree := positive_free_subgraph_endpoint_duality_law
    (G := K) hK hq hpDual hpDual1
  have hfree' :
      (positiveFKLaw K q pDual hq hpDual hpDual1 (BoundaryCondition.free ∅)).map d =
        positiveFKLaw A q p hq hp hp1 ηA := by
    simpa only [J, A, η, ηA, d, pDual,
      dualParameter_involutive hq hp hp1] using hfree
  have hrename := positiveFKLaw_eq_of_partition_eq
    (G := A.map e.toEmbedding) hq hp hp1
    (positiveBoundaryTransport e ηA) ξ hξ
  have hforward :
      (positiveFKLaw K q pDual hq hpDual hpDual1 (BoundaryCondition.free ∅)).map E =
        positiveFKLaw (A.map e.toEmbedding) q p hq hp hp1 ξ := by
    calc
      _ = ((positiveFKLaw K q pDual hq hpDual hpDual1
          (BoundaryCondition.free ∅)).map d).map f := by
            rw [PMF.map_comp]
            rfl
      _ = (positiveFKLaw A q p hq hp hp1 ηA).map f := by
            rw [hfree']
      _ = positiveFKLaw (A.map e.toEmbedding) q p hq hp hp1 ξ := by
            calc
              _ = positiveFKLaw (A.map e.toEmbedding) q p hq hp hp1
                  (positiveBoundaryTransport e ηA) :=
                    positiveFKLaw_relabel_map hq hp hp1 ηA e
              _ = positiveFKLaw (A.map e.toEmbedding) q p hq hp hp1 ξ := hrename
  have hback :
      (positiveFKLaw (A.map e.toEmbedding) q p hq hp hp1 ξ).map E.symm =
        positiveFKLaw K q pDual hq hpDual hpDual1 (BoundaryCondition.free ∅) := by
    calc
      _ = ((positiveFKLaw K q pDual hq hpDual hpDual1
          (BoundaryCondition.free ∅)).map E).map E.symm := by rw [hforward]
      _ = positiveFKLaw K q pDual hq hpDual hpDual1 (BoundaryCondition.free ∅) := by
            rw [PMF.map_comp]
            have hcomp : E.symm ∘ E = id := by
              funext C
              exact Equiv.symm_apply_apply E C
            rw [hcomp, PMF.map_id]
  simpa only [J, A, d, f, E, pDual] using hback

end
end PottsContinuity.DualityExt
