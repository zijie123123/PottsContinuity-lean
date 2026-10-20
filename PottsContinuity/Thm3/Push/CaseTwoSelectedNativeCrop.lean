module

public import PottsContinuity.Thm3.Push.CaseTwoTraceCrop
public import PottsContinuity.Thm3.Push.CaseTwoPrecursorFirstHitPath
public import PottsContinuity.Thm3.Push.CaseTwoTipFirstHitPath
public import PottsContinuity.Thm3.Push.NativeCaseTwoWalks

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed.FiniteSlit
noncomputable section

/-- Native witnesses decoded with the stored original traces have exactly
the computed retained prefix; no full precursor is selected anew here. -/
theorem caseTwoTraceCrop_eq_of_native_arms
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (precursor : SideCollarFirstHitRecord (9*s) (2*n))
    (D : NativeSourceArms n C
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))))
    (hcolumn : D.column = 4*(s:ℤ))
    (hp : D.paths.first.support = caseTwoPrecursorOriginalTrace n s hfit precursor)
    (hq : D.paths.second.support = caseTwoTipOriginalTrace n s hfit tip) :
    caseTwoTraceCrop n s hfit tip precursor = some (D.paths.first.take D.cropIndex).support := by
  exact caseTwoTraceCrop_eq_of_decoded_firstContact n s hfit C tip precursor
    D.paths.first D.paths.second hp hq D.cropIndex (by simpa only [hcolumn] using D.first_contact)

/-- Every successful concrete selected pair has either intersecting actual
source paths or native geometry preserving both selected ordered traces and
the explicitly computed ray crop. This is pointwise geometry, not locality
on a smaller query set. -/
theorem caseTwo_selected_pair_intersects_or_native_crop
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (precursor : SideCollarFirstHitRecord (9*s) (2*n))
    (htip : caseTwoTipFirstHitSelector n s hfit C = some tip)
    (hprecursor : caseTwoPrecursorFirstHitSelector n s hfit C = some precursor) :
    Nonempty (IntersectingSourceArms (rectangleGraph (0,0) (2*n) (2*n)) C
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ)))) ∨
    ∃ D : NativeSourceArms n C
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))),
      D.column = 4*(s:ℤ) ∧ D.rightColumn = 9*(s:ℤ) ∧
      D.paths.first.support = caseTwoPrecursorOriginalTrace n s hfit precursor ∧
      D.paths.second.support = caseTwoTipOriginalTrace n s hfit tip ∧
      caseTwoTraceCrop n s hfit tip precursor = some (D.paths.first.take D.cropIndex).support := by
  classical
  obtain ⟨a,u,p,ha,hal,har,hu,hptrace,hp,_⟩ :=
    caseTwoPrecursorFirstHitSelector_original_path n s hfit C precursor hprecursor
  obtain ⟨b,v,q,hb,hbl,hbr,hv,hqtrace,hq,_⟩ :=
    caseTwoTipFirstHitSelector_original_path n s hfit C tip htip
  change p.val.support = caseTwoPrecursorOriginalTrace n s hfit precursor at hptrace
  change q.val.support = caseTwoTipOriginalTrace n s hfit tip at hqtrace
  by_cases hdis : ∀ z ∈ p.val.support, z ∉ q.val.support
  · obtain ⟨D,hcolumn,hright,hpaths⟩ := sourceCaseTwo_native_arms_of_disjoint_walks n s hs hfit C
      p.val q.val ⟨ha,hal,har⟩ ⟨hb,hbl,hbr⟩ hu hv (fun z hz => (hp z hz).2) hq hdis
    have hDpre : D.paths.first.support = caseTwoPrecursorOriginalTrace n s hfit precursor := by
      exact (congrArg (fun P : SourceWalkPair (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C) =>
        P.first.support) hpaths).trans hptrace
    have hDtip : D.paths.second.support = caseTwoTipOriginalTrace n s hfit tip := by
      exact (congrArg (fun P : SourceWalkPair (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C) =>
        P.second.support) hpaths).trans hqtrace
    exact Or.inr ⟨D,hcolumn,hright,hDpre,hDtip,
      caseTwoTraceCrop_eq_of_native_arms n s hfit C tip precursor D hcolumn hDpre hDtip⟩
  · push Not at hdis
    exact Or.inl ⟨{
      firstStart := a
      secondStart := b
      firstEnd := u
      secondEnd := v
      first := p.val
      second := q.val
      first_in := ⟨ha,hal,har⟩
      second_in := ⟨hb,hbl,hbr⟩
      intersect := hdis }⟩

end
end PottsContinuity.Push
