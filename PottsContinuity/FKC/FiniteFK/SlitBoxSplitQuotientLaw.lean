-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitQuotientLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitEdgeEquiv
public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitGhostMap
public import PottsContinuity.FKC.FiniteFK.SlitBoxQuotientLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The split cover edges identify with the existing slit-box ghost edges by
first projecting to the slit box and then collapsing its wired arc. -/
def slitBoxSplitGhostEdgeEquiv (n : ℕ) :
    (slitBoxSplitCoverGraph n).edgeSet ≃ (slitBoxGhostGraph n).edgeSet :=
  (slitBoxSplitEdgeEquiv n).trans (slitBoxGhostEdgeEquiv n)

theorem slitBoxSplitGhostEdgeEquiv_val (n : ℕ)
    (e : (slitBoxSplitCoverGraph n).edgeSet) :
    (slitBoxSplitGhostEdgeEquiv n e).val =
      Sym2.map (slitBoxSplitGhostMap n) e.val := by
  have hvertex (x : SlitBoxSplitCoverVertex n) :
      slitBoxGhostMap n (slitBoxSplitBaseVertex n x) =
        slitBoxSplitGhostMap n x := by
    cases x with
    | inl u => simp [slitBoxSplitBaseVertex, slitBoxGhostMap,
        slitBoxSplitGhostMap, wiredVertexMap, u.2]
    | inr v =>
        have hv : v.1.1 ∈ slitBoxWiredArc n := v.1.property
        simp [slitBoxSplitBaseVertex, slitBoxGhostMap,
          slitBoxSplitGhostMap, wiredVertexMap]
  change (slitBoxGhostEdgeEquiv n (slitBoxSplitEdgeEquiv n e)).val = _
  rw [slitBoxGhostEdgeEquiv_val, slitBoxSplitEdgeEquiv_val]
  rw [Sym2.map_map]
  congr 1
  funext x
  exact hvertex x

theorem slitBoxSplitLaw_map_ghost (n : ℕ) (q : ClusterWeight) :
    (law (slitBoxSplitCoverGraph n) q
        (BoundaryCondition.wired (slitBoxSplitCoverBoundary n))).map
        (fun A => A.map (slitBoxSplitGhostEdgeEquiv n).toEmbedding) =
      law (slitBoxGhostGraph n) q
        (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n))) := by
  exact wiredVertexQuotient_law_map (slitBoxSplitGhostMap n)
    (slitBoxSplitGhostMap_surjective n) (slitBoxSplitGhostEdgeEquiv n)
    (slitBoxSplitGhostEdgeEquiv_val n)
    (BoundaryCondition.wired (slitBoxSplitCoverBoundary n))
    (slitBoxSplitBoundary_partition_eq_ker_commonGhostMap n) q

end
end PottsContinuity.FKC.FiniteFK
