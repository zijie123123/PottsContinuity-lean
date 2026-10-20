module

public import PottsContinuity.Thm3.Push.SquareRegionSourceClosure
public import PottsContinuity.Thm3.Push.SquareRegionActiveLocality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- After the source interval, a revealed bond incident to a bottom vertex
forces an actual frontier neighbor. A virtual bond below the square supplies
two outside-labelled faces; the resulting frontier step stays in the square. -/
theorem squareRegion_bottom_after_reveal_has_frontier_adj
    (N : ℕ) (l r : ℤ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (hright : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S)
    (u : RectangleVertex (0,0) N N) (hu0 : u.val.2=0) (hur : r < u.val.1)
    (hN : 1 ≤ N)
    (f : (rectangleGraph (0,0) N N).edgeSet)
    (hf : f ∈ squareRegionReveal N S) (huf : u ∈ f.val) :
    ∃ v, (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u v := by
  let b : LatticeBond := ⟨(u.val.1,-1),.vertical⟩
  have hbu : u.val ∈ b.toSym2 := by
    simp only [b,LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,Sym2.mem_iff]
    right
    apply Prod.ext <;> dsimp; omega
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have hbfalse : b.faceBase false ∉ squareRegionCells N S := by
    change (u.val.1-1,-1) ∉ squareRegionCells N S
    exact squareRegionCells_bottom_after_not_mem N r S hright _ (by dsimp at hu; omega)
      (by dsimp at hu; omega) (by omega)
  have hbtrue : b.faceBase true ∉ squareRegionCells N S := by
    change (u.val.1,-1) ∉ squareRegionCells N S
    exact squareRegionCells_bottom_after_not_mem N r S hright _ (by dsimp at hu; omega)
      (by dsimp at hu; omega) (by omega)
  have hbf : u.val ∈ (rectanglePrimalEdgeBond (0,0) N N f).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨u,huf,rfl⟩
  obtain ⟨v,hv⟩ := cellBoundary_mixed_incidence_has_adj (squareRegionCells N S) u.val
    (rectanglePrimalEdgeBond (0,0) N N f) b hbf hbu
    ((mem_squareRegionReveal_iff_cellFaces N S f).mp hf) ⟨hbfalse,hbtrue⟩
  have hvmem := squareRegionCell_neighbor_mem_off_source_top N l r S hleft hright u
    (by omega) (fun _ => Or.inr hur) v hv
  exact ⟨⟨v,hvmem⟩,(squareRegionFrontier_adj_iff_cellBoundary N S u ⟨v,hvmem⟩).mp hv⟩

end
end PottsContinuity.Push
