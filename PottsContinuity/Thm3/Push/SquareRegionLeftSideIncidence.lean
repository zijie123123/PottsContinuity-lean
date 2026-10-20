module

public import PottsContinuity.Thm3.Push.SquareRegionActiveLocality
public import PottsContinuity.Thm3.Push.SquareRegionSideClosure
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Every original left-side vertex is incident to a revealed original
vertical bond when the exterior left face column is in the region. This
includes both physical corners, without using any virtual edge in the reveal. -/
theorem squareRegion_left_side_vertex_incident_reveal
    (N : ℕ) (hN : 1 ≤ N) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ z : RectangleDualVertex (0,0) N N, z.val.1 = -1 → z ∈ S)
    (u : RectangleVertex (0,0) N N) (hux : u.val.1=0) :
    ∃ f ∈ squareRegionReveal N S, u ∈ f.val := by
  let k : ℤ := if u.val.2 < (N : ℤ) then u.val.2 else u.val.2-1
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have hk : 0 ≤ k ∧ k < (N : ℤ) := by
    dsimp [k]
    split_ifs <;> dsimp at hu <;> omega
  let v : RectangleVertex (0,0) N N := ⟨(0,k),by
    rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  let w : RectangleVertex (0,0) N N := ⟨(0,k+1),by
    rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  have hvw : (rectangleGraph (0,0) N N).Adj v w := by
    apply (rectangleGraph_adj_iff (0,0) N N v w).mpr
    change |(0 : ℤ)-0|+|k-(k+1)|=1
    norm_num
  let f : (rectangleGraph (0,0) N N).edgeSet :=
    ⟨s(v,w),(rectangleGraph (0,0) N N).mem_edgeSet.mpr hvw⟩
  let b : LatticeBond := ⟨(0,k),.vertical⟩
  have hbond : rectanglePrimalEdgeBond (0,0) N N f=b := by
    apply LatticeBond.toSym2_injective
    erw [rectanglePrimalEdgeBond_toSym2_public]
    rfl
  refine ⟨f,?_,?_⟩
  · apply (mem_squareRegionReveal_iff_cellFaces N S f).mpr
    left
    rw [hbond]
    change (-1,k) ∈ squareRegionCells N S
    exact squareRegionCells_left_mem N S hleft k (by omega) (by omega)
  · change u ∈ s(v,w)
    apply (Sym2.mem_iff').mpr
    by_cases hy : u.val.2 < (N : ℤ)
    · left
      apply Subtype.ext
      apply Prod.ext
      · exact hux
      · change u.val.2=k
        simp only [k,ite_eq_left hy]
    · right
      apply Subtype.ext
      apply Prod.ext
      · exact hux
      · change u.val.2=k+1
        simp only [k,ite_eq_right hy]
        omega

end
end PottsContinuity.Push
