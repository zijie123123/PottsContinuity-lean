-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeVisitClassification.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteEdgePort
public import PottsContinuity.FKC.Medial.ParafermionicCoverExploration
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgePorts
public import PottsContinuity.FKC.Medial.ParafermionicCoverToggle
public import PottsContinuity.FKC.Medial.PairingPathSupport
public import PottsContinuity.FKC.Medial.ParafermionicCoverZeroVisitPhase
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

/-- False-layer ports on the actual chosen origin exploration path that query
one specified embedded finite edge. -/
def parafermionicCoverFiniteEdgeFalseVisits (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Finset (ParafermionicCoverFinitePort n) :=
  Finset.univ.filter fun c =>
    parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
      (c, false) ∈
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support

theorem parafermionicCoverFiniteEdgeFalseVisits_card_eq_zero_iff (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeFalseVisits n hn A e).card = 0 ↔
      ∀ c : ParafermionicCoverFinitePort n,
        parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
          (c, false) ∉
            (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  classical
  constructor
  · intro hcard c hEdge hVisit
    have hc : c ∈ parafermionicCoverFiniteEdgeFalseVisits n hn A e := by
      simp [parafermionicCoverFiniteEdgeFalseVisits, hEdge, hVisit]
    have hempty : parafermionicCoverFiniteEdgeFalseVisits n hn A e = ∅ :=
      Finset.card_eq_zero.mp hcard
    rw [hempty] at hc
    simp at hc
  · intro hno
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hc
    rcases Finset.mem_filter.mp hc with ⟨_, ⟨hEdge, hVisit⟩⟩
    exact hno c hEdge hVisit

end
end PottsContinuity.FKC.FiniteFK
