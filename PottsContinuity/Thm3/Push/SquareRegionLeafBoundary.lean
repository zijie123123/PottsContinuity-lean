module

public import PottsContinuity.Thm3.Push.SquareRegionSourceClosure
public import PottsContinuity.PD.Duality.LatticeCellBoundaryParity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Every actual frontier leaf lies on the SOURCE interval or on the full
top. The proof uses full cell-boundary even degree and exact neighbor closure;
there is no premise assigning the leaf to a desired boundary class. -/
theorem squareRegion_frontier_leaf_mem_source_or_top
    (N : ℕ) (l r : ℤ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ z ∈ intervalArmLeftDualPorts N l, z ∈ S)
    (hright : ∀ z ∈ intervalArmRightDualPorts N r, z ∉ S)
    (u v : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u v)
    (hunique : ∀ w, (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u w → w=v) :
    u.val.2=(N : ℤ) ∨ u.val.2=0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r := by
  classical
  by_contra hnot
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have htop : u.val.2 < (N : ℤ) := by
    have hne : u.val.2 ≠ (N : ℤ) := fun h => hnot (Or.inl h)
    dsimp at hu
    omega
  have hbottom : u.val.2=0 → u.val.1 < l ∨ r < u.val.1 := by
    intro hzero
    by_cases hl : u.val.1 < l
    · exact Or.inl hl
    by_cases hr : r < u.val.1
    · exact Or.inr hr
    exact (hnot (Or.inr ⟨hzero,by omega,by omega⟩)).elim
  have hneighbors : (latticeCellBoundaryGraph (squareRegionCells N S)).neighborSet u.val = {v.val} := by
    ext z
    constructor
    · intro hz
      have hzb := squareRegionCell_neighbor_mem_off_source_top N l r S hleft hright u htop hbottom z hz
      have hadj := (squareRegionFrontier_adj_iff_cellBoundary N S u ⟨z,hzb⟩).mp hz
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
