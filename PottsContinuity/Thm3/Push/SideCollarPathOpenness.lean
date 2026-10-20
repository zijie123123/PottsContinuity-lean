module

public import PottsContinuity.Thm3.Push.SideCollarPathSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration
noncomputable section

/-- The decoded selected path uses actual open original bonds in both the
sample and its observed open state, preserving its chronological support. -/
theorem sideCollarArmPathSelector_path_in_sample_and_record (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) (rec : SideCollarArmPathRecord w h)
    (hrec : sideCollarArmPathSelector w h l r C = some rec) :
    ∃ a : RectangleVertex (0,0) w h, a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧
    ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
    ∃ p : (openGraph (rectangleGraph (0,0) w h) rec.2.1).Path a b,
      boundaryClusterPathCode rec.2.1 ⟨a,b,p⟩ = rec.2.2 ∧
    ∃ pC : (openGraph (rectangleGraph (0,0) w h) C).Path a b,
    ∃ pR : (openGraph (rectangleGraph (0,0) w h) (C ∩ rec.1)).Path a b,
      pC.val.support = p.val.support ∧ pR.val.support = p.val.support := by
  obtain ⟨hR,hF,a,ha,hal,har,b,hb,p,hp⟩ := sideCollarArmPathSelector_spec w h l r C rec hrec
  have hsubset : rec.2.1 ⊆ C ∩ rec.1 := by
    rw [hR,hF]
    exact sideCollarLeftArmFrontier_subset_open_record w h l r C
  have hCsub : rec.2.1 ⊆ C := hsubset.trans Finset.inter_subset_left
  let pC : (openGraph (rectangleGraph (0,0) w h) C).Path a b :=
    ⟨p.val.mapLe (openGraph_mono hCsub),(SimpleGraph.Walk.isPath_mapLe _).mpr p.property⟩
  let pR : (openGraph (rectangleGraph (0,0) w h) (C ∩ rec.1)).Path a b :=
    ⟨p.val.mapLe (openGraph_mono hsubset),(SimpleGraph.Walk.isPath_mapLe _).mpr p.property⟩
  exact ⟨a,ha,hal,har,b,hb,p,hp,pC,pR,
    SimpleGraph.Walk.support_mapLe_eq_support _ _,SimpleGraph.Walk.support_mapLe_eq_support _ _⟩

end
end PottsContinuity.Push
