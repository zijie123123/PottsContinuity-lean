module

public import PottsContinuity.Thm3.Push.FilledFrontierFrozenBoundary
public import PottsContinuity.Thm3.Push.CellBoundaryMixedIncidence
public import PottsContinuity.Thm3.Push.FilledCellNeighborClosure
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section
local instance activeFrontierEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The filled reveal contains precisely the original bonds incident to at
least one filled upper face. This is an exact true-dual/cell-carrier bridge. -/
theorem mem_filledTopReveal_iff_cellFaces (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (f : (rectangleGraph a w h).edgeSet) :
    f ∈ rectangleFilledTopReveal a w h A ↔
      (rectanglePrimalEdgeBond a w h f).faceBase false ∈ rectangleFilledFaceCells a w h A ∨
      (rectanglePrimalEdgeBond a w h f).faceBase true ∈ rectangleFilledFaceCells a w h A := by
  let d := rectanglePrimalDualEdgeEquiv a w h f
  let u := rectangleDualEdgeSource a w h d
  let v := rectangleDualEdgeTarget a w h d
  have hs : u.val=(rectanglePrimalEdgeBond a w h f).faceBase false :=
    rectangleDualEdgeSource_faceBase a w h d
  have ht : v.val=(rectanglePrimalEdgeBond a w h f).faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h d
  have hsrc := mem_rectangleFilledFaceCells a w h A u
  have htgt := mem_rectangleFilledFaceCells a w h A v
  rw [hs] at hsrc
  rw [ht] at htgt
  apply Iff.trans (b := u ∉ rectangleBottomRegion a w h A ∨ v ∉ rectangleBottomRegion a w h A)
  · rw [rectangleFilledTopReveal, mem_auxiliaryRegionReveal]
    change (∃ t ∈ s(u,v), t ∉ rectangleBottomRegion a w h A) ↔ _
    constructor
    · rintro ⟨t,htm,htc⟩
      rcases (Sym2.mem_iff').mp htm with rfl | rfl
      · exact Or.inl htc
      · exact Or.inr htc
    · rintro (hu | hv)
      · exact ⟨u,(Sym2.mem_iff').mpr (Or.inl rfl),hu⟩
      · exact ⟨v,(Sym2.mem_iff').mpr (Or.inr rfl),hv⟩
  · exact or_congr hsrc.symm htgt.symm

/-- A vertex incident to both a revealed and an unrevealed original bond is
already in the proved frontier/physical-side wired class. Thus active vertices
off that class have no incident revealed edges. -/
theorem active_mixed_vertex_mem_frontier_wiring (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (u : RectangleVertex a w h)
    (f g : (rectangleGraph a w h).edgeSet)
    (hf : f ∈ rectangleFilledTopReveal a w h A) (hg : g ∉ rectangleFilledTopReveal a w h A)
    (huf : u ∈ f.val) (hug : u ∈ g.val) :
    u ∈ filledFrontierWiredVertices a w h A := by
  classical
  by_cases hl : u.val.1=a.1
  · exact Or.inl hl
  by_cases hr : u.val.1=a.1+(w : ℤ)
  · exact Or.inr (Or.inl hr)
  have hprops := (mem_latticeRectangle a u.val w h).mp u.property
  have hleft : a.1 < u.val.1 := by omega
  have hright : u.val.1 < a.1+(w : ℤ) := by omega
  have hbf : u.val ∈ (rectanglePrimalEdgeBond a w h f).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨u,huf,rfl⟩
  have hbg : u.val ∈ (rectanglePrimalEdgeBond a w h g).toSym2 := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact Sym2.mem_map.mpr ⟨u,hug,rfl⟩
  have hupper := (mem_filledTopReveal_iff_cellFaces a w h A f).mp hf
  have hlower :
      (rectanglePrimalEdgeBond a w h g).faceBase false ∉ rectangleFilledFaceCells a w h A ∧
      (rectanglePrimalEdgeBond a w h g).faceBase true ∉ rectangleFilledFaceCells a w h A := by
    simpa only [mem_filledTopReveal_iff_cellFaces,not_or] using hg
  obtain ⟨t,hcell⟩ := cellBoundary_mixed_incidence_has_adj _ u.val _ _ hbf hbg hupper hlower
  have ht := filledCell_neighbor_mem_rectangle_off_sides a w h A hA u hleft hright t hcell
  let v : RectangleVertex a w h := ⟨t,ht⟩
  have hadj := (filledTopFrontier_adj_iff_cellBoundary a w h A u v).mp hcell
  let e : (rectangleGraph a w h).edgeSet :=
    ⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr (openGraph_le _ _ hadj)⟩
  have he : e ∈ rectangleFilledTopFrontier a w h A :=
    (coe_mem_openEdges_iff _ _ e).mp ((openGraph_adj _ _ u v).mp hadj)
  exact Or.inr (Or.inr ⟨e,he,(Sym2.mem_iff').mpr (Or.inl rfl)⟩)

end
end PottsContinuity.Push
