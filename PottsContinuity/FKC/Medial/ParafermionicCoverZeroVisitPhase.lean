-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverZeroVisitPhase.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhase
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationToggleAvoidance
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

/-- If the actual old exploration path has no false-layer visit querying a
specified embedded finite edge, then all false-layer ports querying that edge
have zero phase atom both before and after toggling it. The second assertion
uses the proved ordered-support stability theorem; no invariance of the FK law
under the toggle is asserted. -/
theorem parafermionicCoverPathPhaseAtom_eq_zero_of_no_false_edge_visit
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hno : ∀ c : ParafermionicCoverFinitePort n,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
        (c, false) ∉ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :
    ∀ c : ParafermionicCoverFinitePort n,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
      parafermionicCoverPathPhaseAtom q n hn A (c, false) = 0 ∧
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
        (c, false) = 0 := by
  classical
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  let p' := parafermionicCoverFiniteOriginExplorationPath n hn
    (toggleEdgeConfiguration e A)
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hp' : p'.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn
    (toggleEdgeConfiguration e A)
  have havoid : ∀ d : ParafermionicCoverFinitePort n,
      (d, false) ∈ p.support →
        parafermionicCoverPortEdge d.1 ≠ parafermionicCoverFiniteEdgeEmbedding n e := by
    intro d hd heq
    exact (hno d heq) (by simpa [p] using hd)
  have hsupp := parafermionicCoverFiniteCornerCut_toggle_same_support_of_no_false_visit
    n hn A e p hp havoid p' hp'
  intro c hc
  have hnot : (c, false) ∉ p.support := by
    simpa [p] using hno c hc
  have hnot' : (c, false) ∉ p'.support := by
    rw [hsupp]
    exact hnot
  constructor
  · simp [parafermionicCoverPathPhaseAtom, p, hnot]
  · simp [parafermionicCoverPathPhaseAtom, p', hnot']

end
end PottsContinuity.FKC.FiniteFK
