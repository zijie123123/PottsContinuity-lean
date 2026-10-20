module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.ActualPrefixQueryContainment

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration
noncomputable section

/-- The extremal physical selector is local on the exact stopped reveal
`Push.caseTwoStoppedPrefixReveal`. No additional revealed edge or source condition is
required. -/
theorem paddedExtremalConfinedPrefixSelector_isLocal
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) :
    (paddedExtremalConfinedPrefixSelector n s hs hfit).IsLocal := by
  apply paddedExtremalConfinedPrefixSelector_isLocal_of_query_containment n s hs hfit
  intro C b aux hb _ hsel
  exact actual_confined_prefix_query_subset_stoppedReveal n s hs hfit C b
    (aux.map (prefixPaddingRetraction n)) hb
    (prefixAuxExtremalTrace_firstContact n s hs hfit b C aux hsel)

/-- A local confined first-contact selector at the exact ceiling scale
consumed by the final strip-RSW composition. -/
theorem roundedLocalConfinedPrefixSelectorExists :
    ∀ n : ℕ, ∀ hn : 13 ≤ n, RoundedLocalConfinedPrefixSelectorExists n hn := by
  intro n hn
  let hfit := (rounded_source_both_rectangles_fit n (by omega) (by omega)).1
  have hs : 1 ≤ (n+8)/9 := by omega
  exact ⟨paddedExtremalConfinedPrefixSelector n ((n+8)/9) hs hfit,
    paddedExtremalConfinedPrefixSelector_isLocal n ((n+8)/9) hs hfit⟩

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
