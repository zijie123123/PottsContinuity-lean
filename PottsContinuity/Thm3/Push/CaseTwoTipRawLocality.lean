module

public import PottsContinuity.Thm3.Push.EmbeddedRawFirstHit
public import PottsContinuity.Thm3.Push.CaseTwoTipFirstHitSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section
local instance caseTwoTipRawEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Raw original queries for the concrete J-to-left-side tip exploration. -/
def caseTwoTipRawReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  embeddedSideRawFirstHitReveal (5*s) (2*n) ((3*s:ℕ):ℤ)
    (rectangleGraph (0,0) (2*n) (2*n))
    (sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl)
    (sourceBandEmbedding_map_le (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl) C

/-- The actual Case 2 tip record, including its filled query shape, is
fixed by agreement on the smaller raw source-square queries. -/
theorem caseTwoTipFirstHitSelector_eq_of_raw_agreement (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C D : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hstates : D ∩ caseTwoTipRawReveal n s hfit C = C ∩ caseTwoTipRawReveal n s hfit C) :
    caseTwoTipFirstHitSelector n s hfit D = caseTwoTipFirstHitSelector n s hfit C := by
  apply embeddedSideFirstHitSelector_eq_of_raw_agreement
  simpa only [caseTwoTipRawReveal,Finset.ext_iff,Finset.mem_inter] using hstates

/-- For a fixed exterior, only inclusion of the explicit raw tip queries
remains to obtain first-selection locality on that exterior. -/
theorem caseTwoTipFirstHitSelector_eq_of_raw_reveal_subset (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C D R : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hsubset : caseTwoTipRawReveal n s hfit C ⊆ R)
    (hstates : D ∩ R = C ∩ R) :
    caseTwoTipFirstHitSelector n s hfit D = caseTwoTipFirstHitSelector n s hfit C := by
  apply caseTwoTipFirstHitSelector_eq_of_raw_agreement n s hfit C D
  exact recorded_agreement_of_subset C D _ _ hsubset hstates

end
end PottsContinuity.Push
