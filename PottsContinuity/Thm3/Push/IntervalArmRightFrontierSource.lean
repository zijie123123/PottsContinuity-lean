module

public import PottsContinuity.Thm3.Push.IntervalArmRightAttachments
public import PottsContinuity.Thm3.Push.SquareRegionBottomIncidence

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance rightFrontierSourceEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

private theorem reflected_success
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmEvent N l r) :
    (configurationIso (squareArmReflectionIso N)).symm A ∈
      intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) := by
  apply (intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l) _).mp
  simpa only [Equiv.apply_symm_apply,sub_sub_cancel] using hA

/-- Every nontrivial right-frontier vertex connects to the original source
interval by actual right-frontier bonds. -/
theorem intervalArmFilledRight_frontier_adj_vertex_connects_source
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l r A)).Adj u v) :
    ∃ s ∈ intervalArmBottomArc N l r,
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l r A) u s := by
  let e := squareArmReflectionIso N
  let B := (configurationIso e).symm A
  let F := intervalArmFilledLeftFrontier N ((N : ℤ)-r) ((N : ℤ)-l) B
  have hpre : (openGraph (rectangleGraph (0,0) N N) F).Adj (e.symm u) (e.symm v) :=
    (openGraphIso e F).map_rel_iff.mp (by
      change (openGraph _ (configurationIso e F)).Adj (e (e.symm u)) (e (e.symm v))
      simpa only [RelIso.apply_symm_apply] using huv)
  obtain ⟨s,t,hs,ht,hus,hut,_,_⟩ := intervalArmFilled_component_contains_source_and_top_leaves
    N ((N : ℤ)-r) ((N : ℤ)-l) (by omega) (by omega) (by omega)
      B (reflected_success N l r A hA) _ _ hpre
  refine ⟨e s,?_,?_⟩
  · change s.val.2=0 ∧ l ≤ (N : ℤ)-s.val.1 ∧ (N : ℤ)-s.val.1 ≤ r
    change s.val.2=0 ∧ (N : ℤ)-r ≤ s.val.1 ∧ s.val.1 ≤ (N : ℤ)-l at hs
    omega
  · have hm := (actualConnected_configurationIso e F _ _).mpr hus
    simpa only [RelIso.apply_symm_apply] using hm

/-- Before the right source interval, a recorded bond at a bottom vertex
forces an actual right-frontier neighbor, by literal reflection. -/
theorem intervalArmFilledRight_bottom_before_reveal_has_frontier_adj
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N) (hu0 : u.val.2=0) (hul : u.val.1 < l)
    (f : (rectangleGraph (0,0) N N).edgeSet)
    (hf : f ∈ intervalArmFilledRightReveal N l r A) (huf : u ∈ f.val) :
    ∃ v, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l r A)).Adj u v := by
  let e := squareArmReflectionIso N
  let B := (configurationIso e).symm A
  obtain ⟨g,hg,hgf⟩ := Finset.mem_map.mp hf
  have huf' : u ∈ Sym2.map e g.val := by
    have heq : (configurationIsoEdgeEquiv e g).val = f.val := congrArg Subtype.val hgf
    change Sym2.map e g.val = f.val at heq
    rwa [heq]
  have hpre : e.symm u ∈ g.val := by
    obtain ⟨w,hw,hwu⟩ := Sym2.mem_map.mp huf'
    have heq : e.symm u=w := by rw [← hwu]; exact e.symm_apply_apply w
    exact heq.symm ▸ hw
  obtain ⟨hleft,hright⟩ := intervalArmFilled_region_seed_labels N ((N : ℤ)-r) ((N : ℤ)-l)
    (by omega) (by omega) (by omega) B (reflected_success N l r A hA)
  obtain ⟨v,hv⟩ := squareRegion_bottom_after_reveal_has_frontier_adj N ((N : ℤ)-r) ((N : ℤ)-l)
    (intervalArmRightRegion N ((N : ℤ)-r) ((N : ℤ)-l) B)ᶜ hleft hright (e.symm u)
    hu0 (by change (N : ℤ)-l < (N : ℤ)-u.val.1; omega) (by omega) g hg hpre
  rw [← intervalArmFilledLeftFrontier_eq_squareRegionFrontier] at hv
  refine ⟨e v,?_⟩
  have hm := (openGraphIso e _).map_rel_iff.mpr hv
  change (openGraph _ (configurationIso e _)).Adj (e (e.symm u)) (e v) at hm
  simpa only [RelIso.apply_symm_apply] using hm

end
end PottsContinuity.Push
