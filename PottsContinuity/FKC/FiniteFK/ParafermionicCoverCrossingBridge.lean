-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverCrossingBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSameSheetBridge
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverUpperBridge
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- A cover walk which crosses sheet `k` yields a bottom-split open connection
in the actual restricted primal strip in that sheet. -/
theorem parafermionicCoverCrossingBridge
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (hu : u.val.2 < k) (hv : k < v.val.2) :
    ∃ s t : ParafermionicStripVertex n,
      s.1.2 = 0 ∧ t.1.2 = 0 ∧ 1 ≤ s.1.1 ∧ t.1.1 ≤ 0 ∧
      ActualConnected (ParafermionicStripGraph n)
        (embeddedConfigurationRestriction (ParafermionicStripGraph n)
          (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
          (parafermionicCoverStrip_map_le n k hk) A) s t := by
  obtain ⟨a, b, q, haX, haY, hbX, hbY, hsheet⟩ :=
    parafermionicCoverBoxOpenWalk_same_sheet_bridge n A w k hu hv
  have haX' : 1 ≤ a.val.1.1 := by
    have h : a.val.1.1 = 1 := by simpa [SimpleGraph.Walk.getVert_zero] using haX
    omega
  have haY' : a.val.1.2 < 0 := by
    simpa [SimpleGraph.Walk.getVert_zero] using haY
  have hbX' : b.val.1.1 ≤ 0 := by
    have h : b.val.1.1 = 0 := by simpa [SimpleGraph.Walk.getVert_length] using hbX
    omega
  have hbY' : b.val.1.2 < 0 := by
    simpa [SimpleGraph.Walk.getVert_length] using hbY
  exact parafermionicCoverUpperBridge n hn k hk A a b q haX' haY' hbX' hbY' hsheet

end PottsContinuity.FKC.FiniteFK
