module

public import PottsContinuity.Thm3.Push.CaseTwoTipRawSeparation
public import PottsContinuity.Thm3.Push.CaseTwoSelectedNativeCrop
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Disjoint actual selected arms force positive height of the recorded tip. -/
theorem caseTwo_selected_disjoint_tip_pos
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (precursor : SideCollarFirstHitRecord (9*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n))
    (htip : caseTwoTipFirstHitSelector n s hfit C = some tip)
    (hprecursor : caseTwoPrecursorFirstHitSelector n s hfit C = some precursor)
    (hlast : (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v)
    (hdis : ∀ z ∈ caseTwoPrecursorOriginalTrace n s hfit precursor,
      z ∉ caseTwoTipOriginalTrace n s hfit tip) : 0 < v.val.2 := by
  obtain ⟨a,u,p,ha,hal,har,hu,hptrace,hp,_⟩ :=
    caseTwoPrecursorFirstHitSelector_original_path n s hfit C precursor hprecursor
  obtain ⟨b,t,q,hb,hbl,hbr,ht,hqtrace,hq,_⟩ :=
    caseTwoTipFirstHitSelector_original_path n s hfit C tip htip
  change p.val.support = caseTwoPrecursorOriginalTrace n s hfit precursor at hptrace
  change q.val.support = caseTwoTipOriginalTrace n s hfit tip at hqtrace
  have hlastq : q.val.support.getLast? = some t := by
    rw [List.getLast?_eq_some_getLast q.val.support_ne_nil,SimpleGraph.Walk.getLast_support]
  have htv : t = v := Option.some.inj (hlastq.symm.trans ((congrArg List.getLast? hqtrace).trans hlast))
  subst t
  exact disjoint_openSourceSquare_tip_pos n (4*(s:ℤ)) v.val.2 (9*(s:ℤ)) C
    p.val q.val ha hb hu (by omega) (by omega) (Prod.ext ht rfl)
    (fun z hz => (hq z hz).2) (by simpa only [hptrace,hqtrace] using hdis)

end
end PottsContinuity.Push
