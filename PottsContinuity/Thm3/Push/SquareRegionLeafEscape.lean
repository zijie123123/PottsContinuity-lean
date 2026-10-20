module

public import PottsContinuity.Thm3.Push.SquareRegionActiveLocality
public import PottsContinuity.PD.Duality.LatticeCellBoundaryParity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- A leaf of the restricted original frontier has an actual cell-boundary
neighbor OUTSIDE the square. Otherwise its full cell-boundary degree would be
one, contradicting the unconditional even-degree theorem. -/
theorem squareRegion_frontier_leaf_has_outside_cell_neighbor
    (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N))
    (u v : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u v)
    (hunique : ∀ w, (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u w → w=v) :
    ∃ z : LatticeVertex, (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val z ∧
      z ∉ PD.FK.latticeRectangle (0,0) N N := by
  classical
  by_contra hno
  have hclosed : ∀ z, (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val z →
      z ∈ PD.FK.latticeRectangle (0,0) N N := by
    intro z hz
    by_contra hbad
    exact hno ⟨z,hz,hbad⟩
  have hneighbors : (latticeCellBoundaryGraph (squareRegionCells N S)).neighborSet u.val = {v.val} := by
    ext z
    constructor
    · intro hz
      have hadj := (squareRegionFrontier_adj_iff_cellBoundary N S u ⟨z,hclosed z hz⟩).mp hz
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (hunique _ hadj))
    · intro hz
      have heq := Set.mem_singleton_iff.mp hz
      subst z
      exact (squareRegionFrontier_adj_iff_cellBoundary N S u v).mpr huv
  have heven := latticeCellBoundaryGraph_even_degree (squareRegionCells N S) u.val
  rw [hneighbors,Set.ncard_singleton] at heven
  norm_num at heven

end
end PottsContinuity.Push
