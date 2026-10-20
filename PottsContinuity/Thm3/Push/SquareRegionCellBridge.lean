module

public import PottsContinuity.Thm3.Push.IntervalArmFaceLabel
public import PottsContinuity.Thm3.Push.DualCutCellBoundary
public import PottsContinuity.PD.Duality.RectangleFlowDimension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section
local instance squareRegionCellPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A true-dual region label on the equivalent enlarged face rectangle. -/
def squareRegionFaceLabel (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N))
    (v : RectangleVertex (-1,-1) (N+1) (N+1)) : Bool :=
  decide ((squareExpandedFaceEquiv N).symm v ∈ S)

/-- The actual original bonds separating a chosen true-dual vertex region. -/
def squareRegionFrontier (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) :
    Configuration (rectangleGraph (0,0) N N) :=
  auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv (0,0) N N) (fun v => decide (v ∈ S))

/-- The finite cells of the chosen true-dual region. -/
abbrev squareRegionCells (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) :=
  rectangleLabelFaceCells (-1,-1) (N+1) (N+1) (squareRegionFaceLabel N S)

@[simp] theorem mem_squareRegionCells (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) (v : RectangleDualVertex (0,0) N N) :
    v.val ∈ squareRegionCells N S ↔ v ∈ S := by
  have h := mem_rectangleLabelFaceCells (-1,-1) (N+1) (N+1)
    (squareRegionFaceLabel N S) (squareExpandedFaceEquiv N v)
  exact h.trans (by simp only [squareRegionFaceLabel,Equiv.symm_apply_apply,decide_eq_true_eq])

/-- The region frontier retains exactly the original bonds on the actual
boundary of the reached face cells. -/
theorem mem_squareRegionFrontier_iff_cellBoundary (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) (f : (rectangleGraph (0,0) N N).edgeSet) :
    f ∈ squareRegionFrontier N S ↔
      rectanglePrimalEdgeBond (0,0) N N f ∈ latticeCellBoundaryBonds (squareRegionCells N S) := by
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N f
  let u := rectangleDualEdgeSource (0,0) N N d
  let v := rectangleDualEdgeTarget (0,0) N N d
  have hu : (rectanglePrimalEdgeBond (0,0) N N f).faceBase false ∈ squareRegionCells N S ↔
      u ∈ S := by
    have hm := mem_squareRegionCells N S u
    rw [rectangleDualEdgeSource_faceBase (0,0) N N d] at hm
    exact hm
  have hv : (rectanglePrimalEdgeBond (0,0) N N f).faceBase true ∈ squareRegionCells N S ↔
      v ∈ S := by
    have hm := mem_squareRegionCells N S v
    rw [rectangleDualEdgeTarget_faceBase (0,0) N N d] at hm
    exact hm
  change f ∈ auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
    (fun z => decide (z ∈ S)) ↔ _
  rw [mem_auxiliaryLabelCut_iff _ _ f u v (by rfl),mem_latticeCellBoundaryBonds]
  constructor
  · intro hne heq
    apply hne
    apply decide_eq_decide.mpr
    exact hu.symm.trans ((Iff.of_eq heq.symm).trans hv)
  · intro hne heq
    apply hne
    exact propext (hv.trans ((decide_eq_decide.mp heq).symm.trans hu.symm))

/-- On original square vertices the cell-boundary graph is exactly the open
region frontier, with all actual edge states retained. -/
theorem squareRegionFrontier_adj_iff_cellBoundary (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) (u v : RectangleVertex (0,0) N N) :
    (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val v.val ↔
      (openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S)).Adj u v := by
  classical
  constructor
  · rintro ⟨hbase,b,hb,hpair⟩
    have huv := (rectangleGraph_adj_iff (0,0) N N u v).mpr hbase
    let f : (rectangleGraph (0,0) N N).edgeSet := ⟨s(u,v),(rectangleGraph (0,0) N N).mem_edgeSet.mpr huv⟩
    have hbond : rectanglePrimalEdgeBond (0,0) N N f = b := by
      apply LatticeBond.toSym2_injective
      erw [rectanglePrimalEdgeBond_toSym2_public]
      rw [hpair]
      rfl
    have hf : f ∈ squareRegionFrontier N S := by
      apply (mem_squareRegionFrontier_iff_cellBoundary N S f).mpr
      simpa only [hbond] using hb
    rw [openGraph_adj]
    exact ⟨f,hf,rfl⟩
  · intro hopen
    have huv := openGraph_le (rectangleGraph (0,0) N N) _ hopen
    let f : (rectangleGraph (0,0) N N).edgeSet := ⟨s(u,v),(rectangleGraph (0,0) N N).mem_edgeSet.mpr huv⟩
    have hf : f ∈ squareRegionFrontier N S :=
      (coe_mem_openEdges_iff _ _ f).mp ((openGraph_adj _ _ u v).mp hopen)
    have hb := (mem_squareRegionFrontier_iff_cellBoundary N S f).mp hf
    refine ⟨(rectangleGraph_adj_iff (0,0) N N u v).mp huv,
      rectanglePrimalEdgeBond (0,0) N N f,hb,?_⟩
    erw [rectanglePrimalEdgeBond_toSym2_public]
    rfl

/-- Coordinate-faithful embedding for pulling a confined cell-boundary path
back to the original sampled frontier. -/
def squareRegionFrontierCellEmbedding (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N)) :
    openGraph (rectangleGraph (0,0) N N) (squareRegionFrontier N S) ↪g
      latticeCellBoundaryGraph (squareRegionCells N S) where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro u v
    exact squareRegionFrontier_adj_iff_cellBoundary N S u v

end
end PottsContinuity.Push
