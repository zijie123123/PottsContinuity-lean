/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutTerminalPermutation.lean`.
Adaptation: namespace relocation and canonical source-tip seed labels.
-/
module

public import PottsContinuity.Thm4.EdgeCutTerminalLabels
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial

noncomputable section

def parafermionicCoverFiniteEdgeCutTerminalPermutation (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) : Equiv.Perm (Fin 3) :=
  ((parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e).trans
    (parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn A e)).trans
      (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e).symm

theorem parafermionicCoverFiniteEdgeCutTerminalPermutation_sinkLabel
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) =
      parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1 := by
  change (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1 = _
  have h := Equiv.apply_symm_apply (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e)
    (parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn A e
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i))
  simp [parafermionicCoverFiniteEdgeCutTerminalPermutation,
    parafermionicCoverFiniteEdgeCutSourceSinkEquiv, Equiv.trans_apply]

theorem parafermionicCoverFiniteEdgeCutTerminalPermutation_reachable
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1
      (parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 := by
  exact (parafermionicCoverFiniteEdgeCutPartner_spec n hn A e
    (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).2

theorem parafermionicCoverFiniteEdgeCutSourceSinkEquiv_toggle_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn A e =
      parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn
        (toggleEdgeConfiguration e A) e := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  exact parafermionicCoverFiniteEdgeCutPartner_toggle_eq n hn A e s.1

theorem parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e =
      parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
        (toggleEdgeConfiguration e A) e := by
  unfold parafermionicCoverFiniteEdgeCutTerminalPermutation
  rw [parafermionicCoverFiniteEdgeCutSourceSinkEquiv_toggle_eq]

end
end PottsContinuity.Thm4
