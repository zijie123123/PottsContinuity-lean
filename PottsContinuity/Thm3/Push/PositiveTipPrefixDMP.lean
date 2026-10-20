module

public import PottsContinuity.Thm3.Push.PositiveTipRecordSelector
public import PottsContinuity.Exploration.DependentPairPathDMP

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance positiveTipPrefixEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance positiveTipPrefixRemainingFintype (n : ℕ)
    (R : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) (2*n) (2*n)) R) := Fintype.ofFinite _

/-- The augmented two-sided reveal uses only the directly stopped prefix
and the actual positive tip. No discarded precursor suffix is recorded. -/
def caseTwoStoppedPrefixReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoPositiveTipRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n))) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  pocketAugmentedSourceReveal (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
    (Subtype.val '' {z | z ∈ trace})
    (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit b.1})

/-- The corrected second reveal contains the actual first-stage reveal. -/
theorem caseTwoTipRightReveal_subset_stoppedPrefixReveal
    (n s : ℕ) (hfit : 9*s ≤ 2*n) (b : CaseTwoPositiveTipRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n))) :
    caseTwoTipRightReveal n s hfit b.1 b.2 ⊆ caseTwoStoppedPrefixReveal n s hfit b trace := by
  unfold caseTwoTipRightReveal caseTwoStoppedPrefixReveal pocketAugmentedSourceReveal
  exact Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_right

/-- Compose the actual positive tip with a prefix selected directly from
that tip's stopped domain. The prefix selector is an explicit interface. -/
def caseTwoPositiveTipPrefixRevealMap (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoPositiveTipRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n)))) :
    RevealMap (G := rectangleGraph (0,0) (2*n) (2*n)) :=
  dependentPairPathRevealMap (caseTwoPositiveTipSelector n s hfit) selectPrefix
    (fun b => caseTwoTipRightReveal n s hfit b.1 b.2)
    (caseTwoStoppedPrefixReveal n s hfit)

/-- Actual first-stage locality is discharged. Only the corrected stopped
prefix's selected-value locality remains as an explicit provider interface. -/
theorem caseTwoPositiveTipPrefixRevealMap_stable_of_prefixLocality
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoPositiveTipRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoPositiveTipSelector n s hfit C = some b →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace) :
    ∀ C D, D ∩ caseTwoPositiveTipPrefixRevealMap n s hfit selectPrefix C =
      C ∩ caseTwoPositiveTipPrefixRevealMap n s hfit selectPrefix C →
      caseTwoPositiveTipPrefixRevealMap n s hfit selectPrefix D =
        caseTwoPositiveTipPrefixRevealMap n s hfit selectPrefix C := by
  exact dependentPairPathRevealMap_stable (caseTwoPositiveTipSelector n s hfit) selectPrefix
    (fun b => caseTwoTipRightReveal n s hfit b.1 b.2)
    (caseTwoStoppedPrefixReveal n s hfit)
    (caseTwoPositiveTipSelector_oneSidedStable n s hs hfit) hprefix

end
end PottsContinuity.Push
