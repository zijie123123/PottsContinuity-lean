-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverConnectionAvoidance.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.DisjointBlockEventAvoidance
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverIntermediateLayers
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerBlocks
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchBarrier
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- Any actual cover connection whose endpoint sheets straddle every index in
`J` avoids all corresponding literal layer branch-root events. -/
theorem parafermionicCoverConnection_avoids_straddledLayerBranchRootEvents
    (n : ℕ) (hn : 1 ≤ n) (J : Finset (ParafermionicCoverLayerIndex n))
    {u v : ParafermionicAmbientVertex n}
    (hstraddle : ∀ i ∈ J,
      ((u.val.2 < i.val ∧ i.val < v.val.2) ∨
        (v.val.2 < i.val ∧ i.val < u.val.2))) :
    {A : Configuration (ParafermionicAmbientGraph n) |
      ActualConnected (ParafermionicAmbientGraph n) A u v} ⊆
      disjointBlockAvoidanceSet
        (fun i : ParafermionicCoverLayerIndex n =>
          parafermionicCoverLayerBranchRootEvent n i.val i.property hn) J := by
  intro A hconn i hi hLayer
  obtain ⟨w⟩ := (actualConnected_iff_walk
    (ParafermionicAmbientGraph n) A u v).mp hconn
  rcases hstraddle i hi with hforward | hbackward
  · exact parafermionicCoverLayerBranchRootEvent_not_of_sheetCrossing
      n hn i.val i.property A w hforward.1 hforward.2 hLayer
  · have hnot := parafermionicCoverLayerBranchRootEvent_not_of_sheetCrossing
      n hn i.val i.property A w.reverse hbackward.1 hbackward.2
    exact hnot hLayer

end PottsContinuity.FKC.FiniteFK
