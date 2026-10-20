-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverThreeReturnProbability.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEdgeCutPrimalConnection
public import PottsContinuity.FKC.FiniteFK.CriticalEdgeToggle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The actual three-return weight ratio gives the normalized insert mass for
the same edge and the same finite FK partition function. -/
theorem parafermionicCoverFiniteEdgeCutThreeReturn_insert_probability
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    configurationProbability (ParafermionicAmbientGraph n) q ξ (insert e A) =
      loopWeight q * configurationProbability (ParafermionicAmbientGraph n) q ξ A := by
  have hratio := (parafermionicCoverFiniteEdgeCutThreeReturn_criticalMassRatio
    n hn q ξ A e hclosed hπ0 hπ1).2
  have hweight : weight (ParafermionicAmbientGraph n) q ξ (insert e A) =
      loopWeight q * weight (ParafermionicAmbientGraph n) q ξ A :=
    (div_eq_iff (weight_pos (ParafermionicAmbientGraph n) q ξ A).ne').mp hratio
  unfold configurationProbability
  rw [hweight]
  ring

/-- Under the same actual closed three-return hypotheses, the toggle simply
opens the selected edge, so its normalized mass is multiplied by `loopWeight`. -/
theorem parafermionicCoverFiniteEdgeCutThreeReturn_toggle_probability
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    configurationProbability (ParafermionicAmbientGraph n) q ξ
        (toggleEdgeConfiguration e A) =
      loopWeight q * configurationProbability (ParafermionicAmbientGraph n) q ξ A := by
  have htoggle : insert e A = toggleEdgeConfiguration e A := by
    ext f
    simp [toggleEdgeConfiguration, hclosed]
  rw [← htoggle]
  exact parafermionicCoverFiniteEdgeCutThreeReturn_insert_probability
    n hn q ξ A e hclosed hπ0 hπ1

end
end PottsContinuity.FKC.FiniteFK
