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
local instance intervalCellPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite cells reached by the actual source left-arc exploration. -/
abbrev intervalArmLeftFaceCells (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :=
  rectangleLabelFaceCells (-1,-1) (N+1) (N+1) (intervalArmFaceLabel N l A)

@[simp] theorem mem_intervalArmLeftFaceCells (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) (v : RectangleDualVertex (0,0) N N) :
    v.val ∈ intervalArmLeftFaceCells N l A ↔ v ∈ intervalArmLeftReached N l A := by
  have h := mem_rectangleLabelFaceCells (-1,-1) (N+1) (N+1)
    (intervalArmFaceLabel N l A) (squareExpandedFaceEquiv N v)
  exact h.trans (by simp only [intervalArmFaceLabel,Equiv.symm_apply_apply,decide_eq_true_eq])

/-- The source frontier retains exactly the original bonds on the actual
boundary of the reached face cells. -/
theorem mem_intervalArmLeftFrontier_iff_cellBoundary (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) (f : (rectangleGraph (0,0) N N).edgeSet) :
    f ∈ intervalArmLeftFrontier N l A ↔
      rectanglePrimalEdgeBond (0,0) N N f ∈ latticeCellBoundaryBonds (intervalArmLeftFaceCells N l A) := by
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N f
  let u := rectangleDualEdgeSource (0,0) N N d
  let v := rectangleDualEdgeTarget (0,0) N N d
  have hu : (rectanglePrimalEdgeBond (0,0) N N f).faceBase false ∈ intervalArmLeftFaceCells N l A ↔
      u ∈ intervalArmLeftReached N l A := by
    have hm := mem_intervalArmLeftFaceCells N l A u
    rw [rectangleDualEdgeSource_faceBase (0,0) N N d] at hm
    exact hm
  have hv : (rectanglePrimalEdgeBond (0,0) N N f).faceBase true ∈ intervalArmLeftFaceCells N l A ↔
      v ∈ intervalArmLeftReached N l A := by
    have hm := mem_intervalArmLeftFaceCells N l A v
    rw [rectangleDualEdgeTarget_faceBase (0,0) N N d] at hm
    exact hm
  change f ∈ auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv (0,0) N N)
    (fun z => decide (z ∈ intervalArmLeftReached N l A)) ↔ _
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
source frontier, with all actual edge states retained. -/
theorem intervalArmLeftFrontier_adj_iff_cellBoundary (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) (u v : RectangleVertex (0,0) N N) :
    (latticeCellBoundaryGraph (intervalArmLeftFaceCells N l A)).Adj u.val v.val ↔
      (openGraph (rectangleGraph (0,0) N N) (intervalArmLeftFrontier N l A)).Adj u v := by
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
    have hf : f ∈ intervalArmLeftFrontier N l A := by
      apply (mem_intervalArmLeftFrontier_iff_cellBoundary N l A f).mpr
      simpa only [hbond] using hb
    rw [openGraph_adj]
    exact ⟨f,hf,rfl⟩
  · intro hopen
    have huv := openGraph_le (rectangleGraph (0,0) N N) _ hopen
    let f : (rectangleGraph (0,0) N N).edgeSet := ⟨s(u,v),(rectangleGraph (0,0) N N).mem_edgeSet.mpr huv⟩
    have hf : f ∈ intervalArmLeftFrontier N l A :=
      (coe_mem_openEdges_iff _ _ f).mp ((openGraph_adj _ _ u v).mp hopen)
    have hb := (mem_intervalArmLeftFrontier_iff_cellBoundary N l A f).mp hf
    refine ⟨(rectangleGraph_adj_iff (0,0) N N u v).mp huv,
      rectanglePrimalEdgeBond (0,0) N N f,hb,?_⟩
    erw [rectanglePrimalEdgeBond_toSym2_public]
    rfl

/-- Coordinate-faithful embedding for pulling a confined cell-boundary path
back to the original sampled frontier. -/
def intervalArmLeftFrontierCellEmbedding (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    openGraph (rectangleGraph (0,0) N N) (intervalArmLeftFrontier N l A) ↪g
      latticeCellBoundaryGraph (intervalArmLeftFaceCells N l A) where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro u v
    exact intervalArmLeftFrontier_adj_iff_cellBoundary N l A u v

end
end PottsContinuity.Push
