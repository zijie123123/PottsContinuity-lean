module

public import PottsContinuity.Thm3.Push.SquareRegionHorizontalClosure
public import PottsContinuity.PD.Duality.LatticeCellBoundaryParity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- EVERY mixed incidence, including original side/top/bottom/corner
vertices, has an actual original frontier neighbor when N is positive.
If all cell-boundary neighbors escaped, horizontal closure would leave a
single vertical outside neighbor, contradicting even full-cell degree. -/
theorem squareRegion_mixed_incidence_has_frontier_adj_all
    (N : ℕ) (hN : 1 ≤ N) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ z : RectangleDualVertex (0,0) N N, z.val.1 = -1 → z ∈ S)
    (hright : ∀ z : RectangleDualVertex (0,0) N N, z.val.1 = (N : ℤ) → z ∉ S)
    (u : RectangleVertex (0,0) N N)
    (f g : (rectangleGraph (0,0) N N).edgeSet)
    (hf : f ∈ squareRegionReveal N S) (hg : g ∉ squareRegionReveal N S)
    (huf : u ∈ f.val) (hug : u ∈ g.val) :
    ∃ v, (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u v := by
  classical
  have hbf : u.val ∈ (rectanglePrimalEdgeBond (0,0) N N f).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨u,huf,rfl⟩
  have hbg : u.val ∈ (rectanglePrimalEdgeBond (0,0) N N g).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨u,hug,rfl⟩
  have hupper := (mem_squareRegionReveal_iff_cellFaces N S f).mp hf
  have hlower :
      (rectanglePrimalEdgeBond (0,0) N N g).faceBase false ∉ squareRegionCells N S ∧
      (rectanglePrimalEdgeBond (0,0) N N g).faceBase true ∉ squareRegionCells N S := by
    simpa only [mem_squareRegionReveal_iff_cellFaces,not_or] using hg
  obtain ⟨t,ht⟩ := cellBoundary_mixed_incidence_has_adj _ u.val _ _ hbf hbg hupper hlower
  by_contra hno
  have hout : ∀ z, (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val z →
      z ∉ latticeRectangle (0,0) N N := by
    intro z hz hzb
    exact hno ⟨⟨z,hzb⟩,(squareRegionFrontier_adj_iff_cellBoundary N S u ⟨z,hzb⟩).mp hz⟩
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have htu := squareRegionCell_neighbor_horizontal_bounds N S hleft hright u t ht
  have hdistt : |u.val.1-t.1|+|u.val.2-t.2|=1 := latticeCellBoundaryGraph_le _ ht
  have htnobox : ¬ (0 ≤ t.1 ∧ t.1 ≤ (N : ℤ) ∧ 0 ≤ t.2 ∧ t.2 ≤ (N : ℤ)) := by
    intro hb
    apply hout t ht
    rw [mem_latticeRectangle]
    exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩
  have hneighbors : (latticeCellBoundaryGraph (squareRegionCells N S)).neighborSet u.val = {t} := by
    ext z
    constructor
    · intro hz
      have hzu := squareRegionCell_neighbor_horizontal_bounds N S hleft hright u z hz
      have hdistz : |u.val.1-z.1|+|u.val.2-z.2|=1 := latticeCellBoundaryGraph_le _ hz
      have hznobox : ¬ (0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (N : ℤ)) := by
        intro hb
        apply hout z hz
        rw [mem_latticeRectangle]
        exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩
      apply Set.mem_singleton_iff.mpr
      simp only [abs_eq_max_neg] at hdistt hdistz
      dsimp at hu
      apply Prod.ext <;> omega
    · intro hz
      have heq := Set.mem_singleton_iff.mp hz
      subst z
      exact ht
  have heven := latticeCellBoundaryGraph_even_degree (squareRegionCells N S) u.val
  rw [hneighbors,Set.ncard_singleton] at heven
  norm_num at heven

end
end PottsContinuity.Push
