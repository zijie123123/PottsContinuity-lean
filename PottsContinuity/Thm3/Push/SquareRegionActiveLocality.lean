module

public import PottsContinuity.Thm3.Push.FilledFrontierDMP
public import PottsContinuity.Thm3.Push.SquareRegionCellBridge
public import PottsContinuity.Thm3.Push.CellBoundaryMixedIncidence
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Every original bond incident to the chosen true-dual face region. -/
abbrev squareRegionReveal (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) :=
  auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv (0,0) N N) S

/-- The reveal is exactly incidence to either of the two literal face cells. -/
theorem mem_squareRegionReveal_iff_cellFaces (N : ℕ)
    (S : Set (RectangleDualVertex (0,0) N N)) (f : (rectangleGraph (0,0) N N).edgeSet) :
    f ∈ squareRegionReveal N S ↔
      (rectanglePrimalEdgeBond (0,0) N N f).faceBase false ∈ squareRegionCells N S ∨
      (rectanglePrimalEdgeBond (0,0) N N f).faceBase true ∈ squareRegionCells N S := by
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N f
  let u := rectangleDualEdgeSource (0,0) N N d
  let v := rectangleDualEdgeTarget (0,0) N N d
  have hs : u.val=(rectanglePrimalEdgeBond (0,0) N N f).faceBase false :=
    rectangleDualEdgeSource_faceBase (0,0) N N d
  have ht : v.val=(rectanglePrimalEdgeBond (0,0) N N f).faceBase true :=
    rectangleDualEdgeTarget_faceBase (0,0) N N d
  have hsrc := mem_squareRegionCells N S u
  have htgt := mem_squareRegionCells N S v
  rw [hs] at hsrc
  rw [ht] at htgt
  apply Iff.trans (b := u ∈ S ∨ v ∈ S)
  · rw [squareRegionReveal,mem_auxiliaryRegionReveal]
    change (∃ t ∈ s(u,v), t ∈ S) ↔ _
    constructor
    · rintro ⟨t,htm,htc⟩
      rcases (Sym2.mem_iff').mp htm with rfl | rfl
      · exact Or.inl htc
      · exact Or.inr htc
    · rintro (hu | hv)
      · exact ⟨u,(Sym2.mem_iff').mpr (Or.inl rfl),hu⟩
      · exact ⟨v,(Sym2.mem_iff').mpr (Or.inr rfl),hv⟩
  · exact or_congr hsrc.symm htgt.symm

end
end PottsContinuity.Push
