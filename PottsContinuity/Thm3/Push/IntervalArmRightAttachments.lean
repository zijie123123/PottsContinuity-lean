module

public import PottsContinuity.Thm3.Push.IsoMixedIncidence
public import PottsContinuity.Thm3.Push.IntervalArmAllAttachments
public import PottsContinuity.Thm3.Push.IntervalArmRightFrontier

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance rightAttachmentEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- Original square vertices incident to both a right-record bond and a
remaining bond, including physical boundary vertices. -/
def intervalArmFilledRightAttachmentVertices (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) : Set (RectangleVertex (0,0) N N) :=
  {u | ∃ f ∈ intervalArmFilledRightReveal N l r A,
    ∃ g : (rectangleGraph (0,0) N N).edgeSet,
      g ∉ intervalArmFilledRightReveal N l r A ∧ u ∈ f.val ∧ u ∈ g.val}

/-- Reflection identifies literal mixed incidences, including all corners. -/
theorem intervalArmFilledRight_attachment_reflection_iff
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    (u : RectangleVertex (0,0) N N) :
    u ∈ intervalArmFilledRightAttachmentVertices N l r A ↔
    (squareArmReflectionIso N).symm u ∈ intervalArmFilledAttachmentVertices
      N ((N : ℤ)-r) ((N : ℤ)-l) ((configurationIso (squareArmReflectionIso N)).symm A) := by
  have h := mixed_incidence_configurationIso_iff (squareArmReflectionIso N)
    (intervalArmFilledLeftReveal N ((N : ℤ)-r) ((N : ℤ)-l)
      ((configurationIso (squareArmReflectionIso N)).symm A))
    ((squareArmReflectionIso N).symm u)
  simpa only [RelIso.apply_symm_apply, intervalArmFilledRightAttachmentVertices,
    intervalArmFilledAttachmentVertices, intervalArmFilledRightReveal, isoStoppingReveal,
    Set.mem_ofPred_eq] using h

private theorem reflected_success
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmEvent N l r) :
    (configurationIso (squareArmReflectionIso N)).symm A ∈
      intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) := by
  apply (intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l) _).mp
  simpa only [Equiv.apply_symm_apply,sub_sub_cancel] using hA

/-- Every two right attachments connect by actual recorded-open frontier
bonds; no induced boundary relation is supplied as a premise. -/
theorem intervalArmFilledRight_attachment_vertices_connected
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v : RectangleVertex (0,0) N N)
    (hu : u ∈ intervalArmFilledRightAttachmentVertices N l r A)
    (hv : v ∈ intervalArmFilledRightAttachmentVertices N l r A) :
    ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l r A) u v := by
  have hc := intervalArmFilled_attachment_vertices_connected N ((N : ℤ)-r) ((N : ℤ)-l)
    (by omega) (by omega) (by omega) _ (reflected_success N l r A hA)
    _ _ ((intervalArmFilledRight_attachment_reflection_iff N l r A u).mp hu)
    ((intervalArmFilledRight_attachment_reflection_iff N l r A v).mp hv)
  have hm := (actualConnected_configurationIso (squareArmReflectionIso N) _ _ _).mpr hc
  simpa only [RelIso.apply_symm_apply] using hm

/-- Every right attachment joins the original source interval by actual
right-frontier bonds, without replacing it by the full bottom side. -/
theorem intervalArmFilledRight_attachment_connects_source
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N)
    (hu : u ∈ intervalArmFilledRightAttachmentVertices N l r A) :
    ∃ s ∈ intervalArmBottomArc N l r,
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l r A) u s := by
  obtain ⟨s,hs,hcs⟩ := intervalArmFilled_attachment_connects_source N ((N : ℤ)-r) ((N : ℤ)-l)
    (by omega) (by omega) (by omega) _ (reflected_success N l r A hA)
    _ ((intervalArmFilledRight_attachment_reflection_iff N l r A u).mp hu)
  refine ⟨squareArmReflectionVertex N s,?_,?_⟩
  · change s.val.2=0 ∧ l ≤ (N : ℤ)-s.val.1 ∧ (N : ℤ)-s.val.1 ≤ r
    change s.val.2=0 ∧ (N : ℤ)-r ≤ s.val.1 ∧ s.val.1 ≤ (N : ℤ)-l at hs
    omega
  · have hm := (actualConnected_configurationIso (squareArmReflectionIso N) _ _ _).mpr hcs
    change ActualConnected _ (configurationIso (squareArmReflectionIso N) _) u
      ((squareArmReflectionIso N) s)
    simpa only [RelIso.apply_symm_apply] using hm

end
end PottsContinuity.Push
