-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceCrossing.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceMembershipPropagation
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCoefficientMembership
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCornerCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleFilling
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open SimpleGraph

/-- The corresponding disagreement criterion is edge membership in the same
actual cycle. -/
theorem parafermionicCoverSimpleCycleFillingSet_adjacent_owner_disagree_iff_edge_mem
    {n : ℕ} (hn : 1 ≤ n) {u₀ : ParafermionicCoverBoxVertex n}
    (C : (parafermionicCoverBoxGraph n).Walk u₀ u₀) (hC : C.IsCycle)
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (u v : ParafermionicCoverBoxVertex n)
    (hforward : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1)
    (hbackward : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts j.1)
    (hS : S = parafermionicCoverSimpleCycleFillingSet hn C hC) :
    ¬ (i ∈ S ↔ j ∈ S) ↔ s(u,v) ∈ C.edges := by
  have hnonzero := parafermionicCoverFaceBoundaryCoefficient_eq_zero_iff_owner_mem_iff
    S i j u v hforward hbackward
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn C hC
  have hcoeff : parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ C.edges := by
    simpa [hS] using (hspec.2.2 u v)
  have hdis : ¬ (i ∈ S ↔ j ∈ S) ↔
      parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 :=
    (not_iff_not.mpr hnonzero).symm
  simpa [not_not] using hdis.trans hcoeff

end PottsContinuity.FKC.Medial
