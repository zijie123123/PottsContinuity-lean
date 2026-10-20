-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBranchBarrier.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverCrossingBridge
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerBlocks
public import PottsContinuity.FKC.Curves.RectangleBranchCrosscutObstruction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

/-- A genuine open cover walk crossing a sheet forces a bottom split in that
sheet. The actual planar primal/dual crosscut then rules out the literal
branch-root event on the corresponding dual restriction. -/
theorem parafermionicCoverLayerBranchRootEvent_not_of_sheetCrossing
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (hu : u.val.2 < k) (hv : k < v.val.2) :
    A ∉ parafermionicCoverLayerBranchRootEvent n k hk hn := by
  intro hlayer
  obtain ⟨s, t, hsBottom, htBottom, hsRight, htLeft, hconn⟩ :=
    parafermionicCoverCrossingBridge n hn k hk A w hu hv
  obtain ⟨p⟩ := (actualConnected_iff_walk
    (ParafermionicStripGraph n)
    (embeddedConfigurationRestriction (ParafermionicStripGraph n)
      (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
      (parafermionicCoverStrip_map_le n k hk) A) s t).mp hconn
  let stripA := embeddedConfigurationRestriction (ParafermionicStripGraph n)
      (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
      (parafermionicCoverStrip_map_le n k hk) A
  have hno : rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n stripA ∉
      parafermionicCoverBranchRootEvent n hn := by
    exact rectangleBranchRootEvent_not_of_openBottomCrossing n hn stripA
      p.reverse htBottom hsBottom htLeft hsRight
  have hrestrict : parafermionicCoverStripDualRestriction n k hk A =
      rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n stripA := by
    change rectanglePrimalDualConfigurationEquiv (-(n : ℤ), 0) (2 * n) n stripA = _
    rw [rectanglePrimalDualConfigurationEquiv_apply]
    rfl
  have hroot : rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n stripA ∈
      parafermionicCoverBranchRootEvent n hn := by
    rw [← hrestrict]
    exact hlayer
  exact hno hroot

end PottsContinuity.FKC.FiniteFK
