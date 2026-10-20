-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPairingRouteInteriorShape.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRoutes
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

/-- The strict interior of each actual refined route: a layer/open edge has no
interior vertex, a closed cap has its named midpoint, and a surviving corner
pair has its three named interior vertices. -/
theorem parafermionicCoverRefinedPairingRoute_interior (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.dropLast =
      match u.2, v.2 with
      | false, false =>
          if parafermionicCoverPortBondState
              (parafermionicCoverConfigurationExtensionState n A) u.1.1 then []
          else [parafermionicCoverRefinedClosedCapMiddle u.1.1]
      | true, true =>
          [parafermionicCoverRefinedCornerMid₁ u.1.1,
            parafermionicCoverRefinedCornerElbow u.1.1,
            parafermionicCoverRefinedCornerMid₂ u.1.1]
      | _, _ => [] := by
  rcases u with ⟨c, b⟩
  rcases v with ⟨d, b'⟩
  rw [parafermionicCoverRefinedPairingRoute_support]
  cases b <;> cases b'
  · by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c.1
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs]
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs]
  · simp [parafermionicCoverRefinedPairingRouteSupport]
  · simp [parafermionicCoverRefinedPairingRouteSupport]
  · simp [parafermionicCoverRefinedPairingRouteSupport]

/-- An actual false-layer pairing edge joins the source to its state-selected
open or closed port. -/
theorem parafermionicCoverRefinedPairingRoute_false_false_endpoint
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c d : ParafermionicCoverFinitePort n)
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (c, false) (d, false)) :
    (parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c.1 = true ∧
        d.1 = parafermionicCoverOpenPair c.1) ∨
      (parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c.1 = false ∧
        d.1 = parafermionicCoverClosedPair c.1) := by
  classical
  have hpair : parafermionicCoverFiniteLocalPairPerm n A c = d := by
    have h' := (parafermionicCoverFiniteCornerCutPairingGraph_adj_iff n hn
      A (c, false) (d, false)).mp h
    simp only [Bool.false_eq_true, false_and, and_false,
      or_false, true_and] at h'
    rcases h' with hbad | hgood
    · exact False.elim (hbad.2 rfl)
    · exact hgood.1
  have hraw : parafermionicCoverLocalPair
      (parafermionicCoverConfigurationExtensionState n A) c.1 = d.1 := by
    simpa only [parafermionicCoverFiniteLocalPairPerm_val] using
      congrArg Subtype.val hpair
  cases hs : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) c.1 with
  | false =>
      right
      refine ⟨rfl, ?_⟩
      simpa [parafermionicCoverLocalPair, hs] using hraw.symm
  | true =>
      left
      refine ⟨rfl, ?_⟩
      simpa [parafermionicCoverLocalPair, hs] using hraw.symm

/-- A surviving true-layer edge in the corner-cut graph has exactly its actual
corner-paired raw endpoint; the two cut fixed points cannot be edges. -/
theorem parafermionicCoverRefinedPairingRoute_true_true_endpoint
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c d : ParafermionicCoverFinitePort n)
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (c, true) (d, true)) :
    d.1 = parafermionicCoverCornerPair c.1 := by
  classical
  have h' := (parafermionicCoverFiniteCornerCutPairingGraph_adj_iff n hn A
    (c, true) (d, true)).mp h
  simp only [Bool.true_eq_false, false_and, and_false,
    false_or, true_and] at h'
  have hpair : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) c = d := by
    rcases h' with hbad | hgood
    · exact False.elim (hbad.2 rfl)
    · exact hgood.1
  have hne : c ≠ d := by
    rcases h' with hbad | hgood
    · exact False.elim (hbad.2 rfl)
    · exact hgood.2
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  have hnot : ¬ (c = s ∨ c = C s) := by
    intro hterm
    rcases hterm with hs | hs
    · subst c
      have hfix : pairingSingleCutPerm C s
          (parafermionicCoverFiniteCornerPairPerm_involutive n) s = s := by
        simp [pairingSingleCutPerm_apply, pairingSingleCut, C, s]
      exact hne (hfix.symm.trans hpair)
    · subst c
      have hfix : pairingSingleCutPerm C s
          (parafermionicCoverFiniteCornerPairPerm_involutive n) (C s) = C s := by
        simp [pairingSingleCutPerm_apply, pairingSingleCut, C, s]
      exact hne (hfix.symm.trans hpair)
  have hcut : pairingSingleCutPerm C s
      (parafermionicCoverFiniteCornerPairPerm_involutive n) c = C c := by
    simp [pairingSingleCutPerm_apply, pairingSingleCut, C, s, hnot]
  have hcorner : C c = d := hcut.symm.trans hpair
  calc
    d.1 = (C c).1 := (congrArg Subtype.val hcorner).symm
    _ = parafermionicCoverCornerPair c.1 := by simp [C]

end PottsContinuity.FKC.Medial
