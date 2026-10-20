module

public import PottsContinuity.Thm3.Push.SquareRegionLeafEscape
public import PottsContinuity.Thm3.Push.IntervalArmLeaves
public import PottsContinuity.Thm3.Push.IntervalArmRootRegionBarrier

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- A source leaf of an actual frontier arm has an opposite-region bottom
port at its own column. Even full cell degree supplies the missing downward
edge; the root barrier fixes which of its two adjacent bottom labels is right. -/
theorem intervalArmFilled_source_leaf_has_right_port
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Walk s t)
    (hs : s ∈ intervalArmBottomArc N l r) (ht : t.val.2=(N : ℤ))
    (v : RectangleVertex (0,0) N N)
    (hsv : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj s v)
    (hunique : ∀ w, (openGraph (rectangleGraph (0,0) N N)
      (intervalArmFilledLeftFrontier N l r A)).Adj s w → w=v) :
    ∃ b : RectangleDualVertex (0,0) N N, b.val=(s.val.1,-1) ∧ b ∈ intervalArmRightRegion N l r A := by
  classical
  let S := (intervalArmRightRegion N l r A)ᶜ
  have hF := intervalArmFilledLeftFrontier_eq_squareRegionFrontier N l r A
  have hsv' := hsv
  have hunique' := hunique
  rw [hF] at hsv' hunique'
  obtain ⟨z,hz,hzout⟩ := squareRegion_frontier_leaf_has_outside_cell_neighbor N S s v hsv' hunique'
  have hsbox := (mem_latticeRectangle (0,0) s.val N N).mp s.property
  have hdist : |s.val.1-z.1|+|s.val.2-z.2|=1 := latticeCellBoundaryGraph_le _ hz
  have hznot : ¬ (0 ≤ z.1 ∧ z.1 ≤ (N : ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (N : ℤ)) := by
    intro hb
    apply hzout
    rw [mem_latticeRectangle]
    exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩
  have hs0 := hs.1
  have hsrange := hs.2
  simp only [abs_eq_max_neg] at hdist
  have hzx : z.1=s.val.1 := by dsimp at hsbox; omega
  have hzy : z.2 = -1 := by dsimp at hsbox; omega
  have hstep : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj
      (s.val.1,-1) (s.val.1,(-1 : ℤ)+1) := by
    convert hz.symm using 1 <;> (apply Prod.ext <;> dsimp <;> omega)
  have hcut := (cellBoundary_adj_up_iff _ s.val.1 (-1)).mp hstep
  let dL : RectangleDualVertex (0,0) N N := (squareExpandedFaceEquiv N).symm
    ⟨(s.val.1-1,-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  let dR : RectangleDualVertex (0,0) N N := (squareExpandedFaceEquiv N).symm
    ⟨(s.val.1,-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  have hdL : dL ∈ intervalArmLeftDualPorts N s.val.1 := by
    apply (mem_intervalArmLeftDualPorts N s.val.1 dL).mpr
    exact Or.inr ⟨rfl,by change s.val.1-1 < s.val.1; omega⟩
  have hnotL := intervalArmRightRegion_avoids_left_of_frontier_root N l r hl hr A p
    hs.1 ht hs.2.1 hs.2.2 dL hdL
  have hcellL : (s.val.1-1,-1) ∈ squareRegionCells N S :=
    (mem_squareRegionCells N S dL).mpr hnotL
  have hcellRnot : (s.val.1,-1) ∉ squareRegionCells N S := by
    intro hcellR
    exact hcut (propext ⟨fun _ => hcellL,fun _ => hcellR⟩)
  have hdR : dR ∈ intervalArmRightRegion N l r A := by
    by_contra hnot
    exact hcellRnot ((mem_squareRegionCells N S dR).mpr hnot)
  exact ⟨dR,rfl,hdR⟩

end
end PottsContinuity.Push
