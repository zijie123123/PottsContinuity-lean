module

public import PottsContinuity.Thm3.Push.AllHeightTipRecordSelector
public import PottsContinuity.Thm3.Push.CaseTwoDisjointTipLocality

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- A full first source arm and the actual tip either already connect the
source intervals or supply positive-height native geometry in the base sample.
No full-arm witness is required in any later record fiber. -/
theorem caseTwoTipEndpoint_source_connection_or_native
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hE : C ∈ sourceCaseTwoFirstArm n s) :
    C ∈ arcsConnectionEvent (rectangleGraph (0,0) (2*n) (2*n))
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))) ∨
    ∃ D : NativeSourceArms n C
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))),
      D.column = 4*(s:ℤ) ∧ D.rightColumn = 9*(s:ℤ) ∧
      D.paths.secondEnd = b.2 ∧
      D.paths.second.support = caseTwoTipOriginalTrace n s hfit b.1 ∧ 0 < b.2.val.2 := by
  classical
  obtain ⟨htip,hlast⟩ := (caseTwoTipEndpointSelector_eq_some_iff n s hfit C b.1 b.2).mp hb
  have hsuccess := (caseTwoPrecursorFirstHitSelector_isSome_iff n s hfit C).mpr hE
  cases hpre : caseTwoPrecursorFirstHitSelector n s hfit C with
  | none => simp only [hpre,Option.isSome_none,Bool.false_eq_true] at hsuccess
  | some precursor =>
    rcases caseTwo_selected_pair_intersects_or_native_crop n s hs hfit C b.1 precursor htip hpre with hconn | ⟨D,hcolumn,hright,hp,hq,hcrop⟩
    · exact Or.inl hconn.some.connects
    · right
      have hdis : ∀ z ∈ caseTwoPrecursorOriginalTrace n s hfit precursor,
          z ∉ caseTwoTipOriginalTrace n s hfit b.1 := by
        rw [← hp,← hq]
        exact D.disjoint
      have hy := caseTwo_selected_disjoint_tip_pos n s hs hfit C b.1 precursor b.2
        htip hpre hlast hdis
      have hend : D.paths.second.support.getLast? = some D.paths.secondEnd := by
        rw [List.getLast?_eq_some_getLast D.paths.second.support_ne_nil,SimpleGraph.Walk.getLast_support]
      have hv : D.paths.secondEnd = b.2 :=
        Option.some.inj (hend.symm.trans ((congrArg List.getLast? hq).trans hlast))
      exact ⟨D,hcolumn,hright,hv,hq,hy⟩

end
end PottsContinuity.Push
