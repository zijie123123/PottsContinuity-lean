module

public import PottsContinuity.Thm3.Push.RectangleFilledFrontier
public import PottsContinuity.PD.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance filledCellsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance filledCellsFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _

/-- The filled upper face region on the actual integer cell-base carrier.
Only expanded rectangle faces are included; this is a finite cell set. -/
def rectangleFilledFaceCells (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Finset LatticeVertex :=
  (Finset.univ.filter fun v : RectangleDualVertex a w h =>
    v ∉ rectangleBottomRegion a w h A).map (Function.Embedding.subtype _)

theorem mem_rectangleFilledFaceCells (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (v : RectangleDualVertex a w h) :
    v.val ∈ rectangleFilledFaceCells a w h A ↔ v ∉ rectangleBottomRegion a w h A := by
  classical
  constructor
  · intro hv
    obtain ⟨z,hz,hzv⟩ := Finset.mem_map.mp hv
    have heq : z = v := Subtype.ext hzv
    simpa only [heq, Finset.mem_filter, Finset.mem_univ, true_and] using hz
  · intro hv
    exact Finset.mem_map.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hv,rfl⟩

/-- Membership in the filled primal frontier is exactly membership in the
literal cell boundary of the filled true-dual face region. -/
theorem mem_filledTopFrontier_iff_cellBoundary (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (f : (rectangleGraph a w h).edgeSet) :
    f ∈ rectangleFilledTopFrontier a w h A ↔
      rectanglePrimalEdgeBond a w h f ∈ latticeCellBoundaryBonds (rectangleFilledFaceCells a w h A) := by
  let d := rectanglePrimalDualEdgeEquiv a w h f
  let u := rectangleDualEdgeSource a w h d
  let v := rectangleDualEdgeTarget a w h d
  have hu : (rectanglePrimalEdgeBond a w h f).faceBase false ∈ rectangleFilledFaceCells a w h A ↔
      u ∉ rectangleBottomRegion a w h A := by
    have hmem := mem_rectangleFilledFaceCells a w h A u
    have hc : u.val = (rectanglePrimalEdgeBond a w h f).faceBase false :=
      rectangleDualEdgeSource_faceBase a w h d
    rw [hc] at hmem
    exact hmem
  have hv : (rectanglePrimalEdgeBond a w h f).faceBase true ∈ rectangleFilledFaceCells a w h A ↔
      v ∉ rectangleBottomRegion a w h A := by
    have hmem := mem_rectangleFilledFaceCells a w h A v
    have hc : v.val = (rectanglePrimalEdgeBond a w h f).faceBase true :=
      rectangleDualEdgeTarget_faceBase a w h d
    rw [hc] at hmem
    exact hmem
  change f ∈ auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h)
    (fun z => decide (z ∉ rectangleBottomRegion a w h A)) ↔ _
  rw [mem_auxiliaryLabelCut_iff _ _ f u v (by rfl), mem_latticeCellBoundaryBonds]
  constructor
  · intro hne heq
    apply hne
    apply decide_eq_decide.mpr
    exact hu.symm.trans ((Iff.of_eq heq.symm).trans hv)
  · intro hne heq
    apply hne
    exact propext (hv.trans ((decide_eq_decide.mp heq).symm.trans hu.symm))

end
end PottsContinuity.Push
