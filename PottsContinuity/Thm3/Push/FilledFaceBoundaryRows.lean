module

public import PottsContinuity.Thm3.Push.FilledFaceCells
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Literal vertical cell-boundary adjacency. Proof adapted from the private
boundaryAdj_up in PD/Duality/LatticeCellBoundaryParity.lean. -/
theorem cellBoundary_adj_up_iff (S : Finset LatticeVertex) (x y : ℤ) :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y+1) ↔
      ((x,y) ∈ S) ≠ ((x-1,y) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨_,e,he,hfaces⟩
    rcases e with ⟨⟨a,b⟩,axis⟩
    cases axis with
    | horizontal =>
      simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target] at he
      omega
    | vertical =>
      simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target] at he
      have hab : a=x ∧ b=y := by omega
      rcases hab with ⟨rfl,rfl⟩
      simpa [LatticeBond.faceBase] using hfaces
  · intro hcut
    refine ⟨?_,⟨⟨(x,y),.vertical⟩,?_,?_⟩⟩
    · simp [squareLattice_adj_iff]
    · simp [LatticeBond.toSym2,LatticeBond.source,LatticeBond.target]
    · simpa [LatticeBond.faceBase] using hcut

/-- The whole upper port row belongs to the filled face region. -/
theorem rectangleFilledFaceCells_top (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (x : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1+(w : ℤ)) :
    (x,a.2+(h : ℤ)) ∈ rectangleFilledFaceCells a w h A := by
  let i := (x-a.1).toNat
  have hcast : (i : ℤ) = x-a.1 := Int.toNat_of_nonneg (by omega)
  have hi : i < w := by omega
  let v := rectangleDualTopPortVertex a w h i
  have hv : v ∈ rectangleDualTopPorts a w h :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  have hcoords : v.val = (x,a.2+(h : ℤ)) := by
    simp only [v,rectangleDualTopPortVertex,Nat.min_eq_left hi.le]
    exact Prod.ext (by omega) rfl
  rw [← hcoords,mem_rectangleFilledFaceCells]
  intro hbot
  exact (outsideSeedRegion_subset_compl _ _ _ hbot) (rectangleTopReached_top a w h A hv)

/-- On the crossing event the entire lower port row is outside the filled
face region. Both endpoints of any potential downward escape see this row. -/
theorem rectangleFilledFaceCells_bottom_not_mem (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h) (x : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1+(w : ℤ)) :
    (x,a.2-1) ∉ rectangleFilledFaceCells a w h A := by
  let i := (x-a.1).toNat
  have hcast : (i : ℤ) = x-a.1 := Int.toNat_of_nonneg (by omega)
  have hi : i < w := by omega
  let v := rectangleDualBottomPortVertex a w h i
  have hv : v ∈ rectangleDualBottomPorts a w h :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  have hcoords : v.val = (x,a.2-1) := by
    simp only [v,rectangleDualBottomPortVertex,Nat.min_eq_left hi.le]
    exact Prod.ext (by omega) rfl
  rw [← hcoords,mem_rectangleFilledFaceCells]
  exact not_not_intro (mem_outsideSeedRegion_of_seed _ _ _ hv
    (rectangleTopReached_avoids_bottom a w h A hA hv))

end
end PottsContinuity.Push
