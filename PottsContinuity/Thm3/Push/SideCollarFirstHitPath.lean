module

public import PottsContinuity.Thm3.Push.SideCollarFirstHitSelector
public import PottsContinuity.Thm3.Push.SideCollarPathOpenness

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed.FiniteSlit
noncomputable section

/-- The retained trace is the ordered support of an actual simple path in
original observed open bonds, and its only left-side vertex is its endpoint. -/
theorem sideCollarFirstHitSelector_path_in_open_record (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) (record : SideCollarFirstHitRecord w h)
    (hrecord : sideCollarFirstHitSelector w h l r C = some record) :
    ∃ a : RectangleVertex (0,0) w h, a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧
    ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
    ∃ p : (openGraph (rectangleGraph (0,0) w h) (C ∩ record.1)).Path a b,
      p.val.support = record.2 ∧ ∀ z ∈ p.val.support, z.val.1 = 0 → z = b := by
  classical
  obtain ⟨rec,hrec,hcrop⟩ := Option.bind_eq_some_iff.mp hrecord
  obtain ⟨trace,htrace,heq⟩ := Option.map_eq_some_iff.mp hcrop
  cases heq
  obtain ⟨a,ha,hal,har,b,hb,p,hcode,pC,pR,_,hR⟩ :=
    sideCollarArmPathSelector_path_in_sample_and_record w h l r C rec hrec
  have htraceCode : rec.2.2.drop 2 = pR.val.support := by
    rw [hR,← hcode]
    rfl
  have htrace' : firstContactTrace {v | v.val.1 = 0} pR.val.support = some trace := by
    simpa only [htraceCode] using htrace
  obtain ⟨k,hfind,htake⟩ := Option.map_eq_some_iff.mp htrace'
  have hk := (support_findIdx_some_iff_firstContact pR.val {v | v.val.1 = 0} k).mp hfind
  let q : (openGraph (rectangleGraph (0,0) w h) (C ∩ rec.1)).Path a (pR.val.getVert k) :=
    ⟨pR.val.take k,pR.property.take k⟩
  refine ⟨a,ha,hal,har,pR.val.getVert k,hk.2.1,q,?_,?_⟩
  · change (pR.val.take k).support = trace
    rw [SimpleGraph.Walk.support_take]
    exact htake
  · intro z hz hzS
    exact firstContact_prefix_target_unique pR.val {v | v.val.1 = 0} k hk z hz hzS

end
end PottsContinuity.Push
