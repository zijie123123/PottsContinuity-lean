-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitCoverInteriorClosed.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverEnclosure
public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitBoundaryLift
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Every cover-box neighbor of an interior split vertex is represented by an
actual neighbor in the split graph. The arc case chooses the side by the
interior vertex's horizontal position. -/
theorem slitBoxSplitCover_interior_neighbor_closed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxSplitInterior n)
    (v : ParafermionicCoverBoxVertex n)
    (hadj : (parafermionicCoverBoxGraph n).Adj
      (slitBoxSplitCoverEmbedding n hn (Sum.inl u)) v) :
    ∃ y : SlitBoxSplitCoverVertex n,
      slitBoxSplitCoverEmbedding n hn y = v ∧
      (slitBoxSplitCoverGraph n).Adj (Sum.inl u) y := by
  have hcover : parafermionicCoverGraph.Adj
      (slitBoxInteriorCoverLift n u) v.val := by
    have h := hadj
    rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj] at h
    simpa [slitBoxSplitCoverEmbedding, slitBoxSplitCoverMap] using h
  by_cases harc : (v.val.1.1 = 0 ∧ 0 ≤ v.val.1.2 ∧ v.val.1.2 ≤ n)
  · have hvbounds := (parafermionicCoverBoxVertices_mem n v.val).mp v.property
    have hvrect : v.val.1 ∈
        latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
      rw [mem_latticeRectangle]
      constructor <;> constructor <;> omega
    let b : SlitBoxVertex n := ⟨v.val.1, hvrect⟩
    have hbArc : b ∈ slitBoxWiredArc n := by
      rw [mem_slitBoxWiredArc_iff]
      exact harc
    have hslit : (slitBoxGraph n).Adj u.1 b := by
      apply (slitBoxGraph_adj_iff n u.1 b).mpr
      refine ⟨hcover.1, ?_⟩
      intro hboth
      exact u.2 ((mem_slitBoxWiredArc_iff n u.1).mpr hboth.1)
    let side := decide (0 < u.1.val.1)
    let y : SlitBoxSplitCoverVertex n := Sum.inr (⟨b, hbArc⟩, side)
    have hselected : parafermionicCoverGraph.Adj
        (slitBoxInteriorCoverLift n u) (slitBoxSplitCoverMap n y) := by
      simpa [y, side] using slitBoxInteriorCoverLift_adj_arcSide n u b hbArc hslit
    have hvUnique := parafermionicCoverNeighborLift_unique
      (slitBoxInteriorCoverLift n u) b.val v.val rfl hcover
    have hyUnique := parafermionicCoverNeighborLift_unique
      (slitBoxInteriorCoverLift n u) b.val (slitBoxSplitCoverMap n y) (by rfl) hselected
    have hval : v.val = slitBoxSplitCoverMap n y := hvUnique.trans hyUnique.symm
    refine ⟨y, ?_, ?_⟩
    · apply Subtype.ext
      simpa [y, slitBoxSplitCoverEmbedding_val] using hval.symm
    · simpa [y] using slitBoxSplitCoverGraph_interior_arc_adj n u b hbArc hslit
  · obtain ⟨w, hEq⟩ :=
      slitBoxSplitCover_interior_neighbor_enclosed n hn u v hadj harc
    have hwCover : parafermionicCoverGraph.Adj
        (slitBoxInteriorCoverLift n u) (slitBoxInteriorCoverLift n w) := by
      have h := hadj
      rw [parafermionicCoverBoxGraph, SimpleGraph.induce_adj] at h
      rw [← hEq] at h
      simpa [slitBoxSplitCoverEmbedding, slitBoxSplitCoverMap] using h
    have hslit : (slitBoxGraph n).Adj u.1 w.1 :=
      (slitBoxInteriorCoverLift_adj_iff n u w).2 hwCover
    refine ⟨Sum.inl w, hEq, ?_⟩
    exact (slitBoxSplitCoverGraph_interior_adj_iff n u w).2 hslit

end PottsContinuity.FKC.FiniteFK
