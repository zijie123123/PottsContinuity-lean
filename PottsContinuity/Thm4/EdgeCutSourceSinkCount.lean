/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutSourceSinkCount.lean`.
Adaptation: namespace/import relocation only.
-/
module

public import PottsContinuity.Thm4.EdgeCutDirectedPaths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

abbrev ParafermionicCoverFiniteEdgeCutSources (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :=
  {s : ParafermionicCoverFiniteEdgeCutTerminal n hn e //
    parafermionicCoverFiniteEdgeCutSource n hn e s}

abbrev ParafermionicCoverFiniteEdgeCutSinks (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :=
  {s : ParafermionicCoverFiniteEdgeCutTerminal n hn e //
    ¬ parafermionicCoverFiniteEdgeCutSource n hn e s}

local instance edgeCutCountTerminalFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutTerminal n hn e) := by
  classical exact Fintype.ofFinite _

local instance edgeCutCountSourcesFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutSources n hn e) := by
  classical exact Fintype.ofFinite _

local instance edgeCutCountSinksFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutSinks n hn e) := by
  classical exact Fintype.ofFinite _

def parafermionicCoverFiniteEdgeCutSourceSinkEquiv (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSources n hn e ≃
      ParafermionicCoverFiniteEdgeCutSinks n hn e where
  toFun s := ⟨parafermionicCoverFiniteEdgeCutPartner n hn A e s.1,
    fun hp => ((parafermionicCoverFiniteEdgeCutPartner_source_iff_not_source n hn A e s.1).mp hp) s.2⟩
  invFun t := ⟨parafermionicCoverFiniteEdgeCutPartner n hn A e t.1,
    (parafermionicCoverFiniteEdgeCutPartner_source_iff_not_source n hn A e t.1).mpr t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact parafermionicCoverFiniteEdgeCutPartner_involutive n hn A e s.1
  right_inv t := by
    apply Subtype.ext
    exact parafermionicCoverFiniteEdgeCutPartner_involutive n hn A e t.1

theorem parafermionicCoverFiniteEdgeCutSources_card (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype.card (ParafermionicCoverFiniteEdgeCutSources n hn e) = 3 := by
  classical
  let T := ParafermionicCoverFiniteEdgeCutTerminal n hn e
  let P : T → Prop := parafermionicCoverFiniteEdgeCutSource n hn e
  have htotal : Fintype.card T = 6 := by
    simpa [T, ParafermionicCoverFiniteEdgeCutTerminal] using
      parafermionicCoverFiniteEdgeCutTerminals_card n hn e
  have hsplit := Fintype.card_subtype_compl P
  have heq : Fintype.card (ParafermionicCoverFiniteEdgeCutSources n hn e) =
      Fintype.card (ParafermionicCoverFiniteEdgeCutSinks n hn e) :=
    Fintype.card_congr (parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn A e)
  rw [htotal] at hsplit
  rw [hsplit] at heq
  have hsource : Fintype.card (ParafermionicCoverFiniteEdgeCutSources n hn e) =
      Fintype.card {x : T // P x} := rfl
  rw [hsource] at heq
  omega

theorem parafermionicCoverFiniteEdgeCutSinks_card (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype.card (ParafermionicCoverFiniteEdgeCutSinks n hn e) = 3 := by
  classical
  have h := parafermionicCoverFiniteEdgeCutSources_card n hn A e
  rw [← Fintype.card_congr (parafermionicCoverFiniteEdgeCutSourceSinkEquiv n hn A e)]
  exact h

end
end PottsContinuity.Thm4
