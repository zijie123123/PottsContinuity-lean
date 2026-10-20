module

public import PottsContinuity.Thm3.Push.PositiveTipStoppingMap

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- The actual selected tip together with its original last vertex. -/
abbrev CaseTwoPositiveTipRecord (n s : ℕ) :=
  SideCollarFirstHitRecord (5*s) (2*n) × RectangleVertex (0,0) (2*n) (2*n)

/-- Keep exactly successful positive tips, with no precursor completion test. -/
def caseTwoPositiveTipSelector (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (CaseTwoPositiveTipRecord n s) := by
  classical
  exact (caseTwoTipFirstHitSelector n s hfit C).bind fun tip =>
    ((caseTwoTipOriginalTrace n s hfit tip).getLast?).bind fun v =>
      if 0 < v.val.2 then some (tip,v) else none

/-- Positive tip records retain precisely their literal source success data. -/
theorem caseTwoPositiveTipSelector_eq_some_iff
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n)) :
    caseTwoPositiveTipSelector n s hfit C = some (tip,v) ↔
      caseTwoTipFirstHitSelector n s hfit C = some tip ∧
      (caseTwoTipOriginalTrace n s hfit tip).getLast? = some v ∧ 0 < v.val.2 := by
  classical
  constructor
  · intro h
    obtain ⟨r,hr,hw⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w,hw,he⟩ := Option.bind_eq_some_iff.mp hw
    split_ifs at he with hy
    · have heq := Option.some.inj he
      have hrEq : r = tip := congrArg Prod.fst heq
      have hwEq : w = v := congrArg Prod.snd heq
      subst r
      subst w
      exact ⟨hr,hw,hy⟩
  · rintro ⟨htip,hlast,hy⟩
    simp only [caseTwoPositiveTipSelector,htip,Option.bind_some,hlast,ite_eq_left hy]

local instance positiveTipRecordEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The successful positive record is determined by its own right reveal. -/
theorem caseTwoPositiveTipSelector_oneSidedStable
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C D : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoPositiveTipRecord n s)
    (hb : caseTwoPositiveTipSelector n s hfit C = some b)
    (hstates : D ∩ caseTwoTipRightReveal n s hfit b.1 b.2 =
      C ∩ caseTwoTipRightReveal n s hfit b.1 b.2) :
    caseTwoPositiveTipSelector n s hfit D = some b := by
  obtain ⟨htip,hlast,hy⟩ := (caseTwoPositiveTipSelector_eq_some_iff n s hfit C b.1 b.2).mp hb
  apply (caseTwoPositiveTipSelector_eq_some_iff n s hfit D b.1 b.2).mpr
  refine ⟨?_,hlast,hy⟩
  exact caseTwoTipFirstHitSelector_stable_on_right_augmented_of_pos_height
    n s hs hfit C D b.1 b.2 htip hlast hy hstates

end
end PottsContinuity.Push
