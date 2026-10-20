module

public import PottsContinuity.Thm3.Push.SideCollarFirstHitPath

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Every completion of the recorded original states contains the same
simple retained path, with the same endpoints and ordered vertex trace. -/
theorem sideCollarFirstHitSelector_path_openOnFiber (w h : ℕ) (l r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h)) (record : SideCollarFirstHitRecord w h)
    (hrecord : sideCollarFirstHitSelector w h l r C = some record)
    (hstates : D ∩ record.1 = C ∩ record.1) :
    ∃ a : RectangleVertex (0,0) w h, a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧
    ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
    ∃ pC : (openGraph (rectangleGraph (0,0) w h) C).Path a b,
    ∃ pD : (openGraph (rectangleGraph (0,0) w h) D).Path a b,
      pC.val.support = record.2 ∧ pD.val.support = record.2 ∧
      (∀ z ∈ pC.val.support, z.val.1 = 0 → z = b) ∧
      (∀ z ∈ pD.val.support, z.val.1 = 0 → z = b) := by
  classical
  obtain ⟨a,ha,hal,har,b,hb,p,hp,hfirst⟩ :=
    sideCollarFirstHitSelector_path_in_open_record w h l r C record hrecord
  have hsubC : C ∩ record.1 ⊆ C := Finset.inter_subset_left
  have hsubD : C ∩ record.1 ⊆ D := by
    intro e he
    have hd : e ∈ D ∩ record.1 := by rw [hstates]; exact he
    exact (Finset.mem_inter.mp hd).1
  let pC : (openGraph (rectangleGraph (0,0) w h) C).Path a b :=
    ⟨p.val.mapLe (openGraph_mono hsubC),(SimpleGraph.Walk.isPath_mapLe _).mpr p.property⟩
  let pD : (openGraph (rectangleGraph (0,0) w h) D).Path a b :=
    ⟨p.val.mapLe (openGraph_mono hsubD),(SimpleGraph.Walk.isPath_mapLe _).mpr p.property⟩
  have hC : pC.val.support = p.val.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hD : pD.val.support = p.val.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  exact ⟨a,ha,hal,har,b,hb,pC,pD,hC.trans hp,hD.trans hp,
    by simpa only [hC] using hfirst,by simpa only [hD] using hfirst⟩

end
end PottsContinuity.Push
