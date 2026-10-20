-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverExplorationOrientation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExploration
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import PottsContinuity.FKC.Medial.ParafermionicCoverPortOrientation
public import PottsContinuity.FKC.Medial.PairingPathSupport
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial SimpleGraph
open LatticePort
noncomputable section

local instance coverOrientationAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

/-- The direction on an actual edge of the finite cut pairing graph, determined
by the primal-left orientation of its retained port occurrence. -/
def parafermionicCoverFinitePairingForward (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) : Prop :=
  match u.2, v.2 with
  | false, false =>
      parafermionicCoverIncomingPrimalLeft u.1.1 = true ∧
        parafermionicCoverFiniteLocalPairPerm n A u.1 = v.1
  | true, true =>
      parafermionicCoverIncomingPrimalLeft u.1.1 = false ∧
        pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
          (parafermionicCoverFiniteOriginCornerPort n hn)
          (parafermionicCoverFiniteCornerPairPerm_involutive n) u.1 = v.1 ∧
        u.1 ≠ v.1
  | false, true =>
      parafermionicCoverIncomingPrimalLeft u.1.1 = false ∧ u.1 = v.1
  | true, false =>
      parafermionicCoverIncomingPrimalLeft u.1.1 = true ∧ u.1 = v.1

theorem parafermionicCoverFiniteCornerCutPairingGraph_adj_iff (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v ↔
      (u.1 = v.1 ∧ u.2 ≠ v.2) ∨
      (u.2 = false ∧ v.2 = false ∧
        parafermionicCoverFiniteLocalPairPerm n A u.1 = v.1 ∧ u.1 ≠ v.1) ∨
      (u.2 = true ∧ v.2 = true ∧
        pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
          (parafermionicCoverFiniteOriginCornerPort n hn)
          (parafermionicCoverFiniteCornerPairPerm_involutive n) u.1 = v.1 ∧
        u.1 ≠ v.1) := Iff.rfl

theorem parafermionicCoverFinitePairingForward_implies_adj (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : parafermionicCoverFinitePairingForward n hn A u v) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  all_goals simp only [parafermionicCoverFinitePairingForward] at h
  · rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp only [Bool.false_eq_true, false_and, or_false, true_and]
    rcases h with ⟨_, huv⟩
    have hne : u ≠ v := by
      intro heq
      exact parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A u
        (huv.trans heq.symm)
    exact Or.inr ⟨huv, hne⟩
  · rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, or_false,
      true_and]
    exact ⟨h.2, by decide⟩
  · rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, or_false,
      true_and]
    exact ⟨h.2, by decide⟩
  · rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp only [Bool.true_eq_false, false_and,
      false_or, true_and]
    rcases h with ⟨_, huv, hne⟩
    exact Or.inr ⟨huv, hne⟩

private theorem parafermionicCoverFiniteCutCorner_eq_corner_of_ne
    (n : ℕ) (hn : 1 ≤ n) {u v : ParafermionicCoverFinitePort n}
    (h : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) u = v)
    (hne : u ≠ v) : parafermionicCoverFiniteCornerPairPerm n u = v := by
  have hc : ¬ (u = parafermionicCoverFiniteOriginCornerPort n hn ∨
      u = parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) := by
    intro hc
    have hfix : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n) u = u := by
      rcases hc with hs | hs
      · subst u
        simp [pairingSingleCutPerm_apply, pairingSingleCut]
      · have hback : parafermionicCoverFiniteCornerPairPerm n
            (parafermionicCoverFiniteCornerPairPerm n
              (parafermionicCoverFiniteOriginCornerPort n hn)) =
              parafermionicCoverFiniteOriginCornerPort n hn :=
          parafermionicCoverFiniteCornerPairPerm_involutive n _
        subst u
        simp [pairingSingleCutPerm_apply, pairingSingleCut]
    exact hne (h.symm.trans hfix).symm
  simpa [pairingSingleCutPerm_apply, pairingSingleCut, hc] using h

theorem parafermionicCoverFinitePairing_adj_or_forward (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    parafermionicCoverFinitePairingForward n hn A u v ∨
      parafermionicCoverFinitePairingForward n hn A v u := by
  rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff] at h
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  · rcases h with hvertical | hlocal | hcorner
    · simp at hvertical
    · rcases hlocal with ⟨_, _, hpair, hne⟩
      change parafermionicCoverFiniteLocalPairPerm n A u = v at hpair
      change u ≠ v at hne
      simp only [parafermionicCoverFinitePairingForward]
      have hflip : parafermionicCoverIncomingPrimalLeft
          (parafermionicCoverFiniteLocalPairPerm n A u).1 =
            !parafermionicCoverIncomingPrimalLeft u.1 := by
        simpa only [parafermionicCoverFiniteLocalPairPerm_val] using
          parafermionicCoverIncomingPrimalLeft_localPair
            (parafermionicCoverConfigurationExtensionState n A) u.1
      have hvflip : parafermionicCoverIncomingPrimalLeft v.1 =
          !parafermionicCoverIncomingPrimalLeft u.1 := by
        rw [← hpair]
        exact hflip
      by_cases hu : parafermionicCoverIncomingPrimalLeft u.1 = true
      · exact Or.inl ⟨hu, hpair⟩
      · have hu' : parafermionicCoverIncomingPrimalLeft u.1 = false := by
          cases h' : parafermionicCoverIncomingPrimalLeft u.1 <;> simp_all
        have hv : parafermionicCoverIncomingPrimalLeft v.1 = true := by
          simpa [hu'] using hvflip
        have hrev : parafermionicCoverFiniteLocalPairPerm n A v = u := by
          rw [← hpair]
          exact parafermionicCoverFiniteLocalPairPerm_involutive n A u
        exact Or.inr ⟨hv, hrev⟩
    · simp at hcorner
  · rcases h with hvertical | hlocal | hcorner
    · rcases hvertical with ⟨hport, _⟩
      change u = v at hport
      simp only [parafermionicCoverFinitePairingForward]
      subst v
      by_cases hu : parafermionicCoverIncomingPrimalLeft u.1 = false
      · exact Or.inl ⟨hu, rfl⟩
      · have hu' : parafermionicCoverIncomingPrimalLeft u.1 = true := by
          cases h' : parafermionicCoverIncomingPrimalLeft u.1 <;> simp_all
        exact Or.inr ⟨hu', rfl⟩
    · simp at hlocal
    · simp at hcorner
  · rcases h with hvertical | hlocal | hcorner
    · rcases hvertical with ⟨hport, _⟩
      change u = v at hport
      simp only [parafermionicCoverFinitePairingForward]
      subst v
      by_cases hu : parafermionicCoverIncomingPrimalLeft u.1 = false
      · exact Or.inr ⟨hu, rfl⟩
      · have hu' : parafermionicCoverIncomingPrimalLeft u.1 = true := by
          cases h' : parafermionicCoverIncomingPrimalLeft u.1 <;> simp_all
        exact Or.inl ⟨hu', rfl⟩
    · simp at hlocal
    · simp at hcorner
  · rcases h with hvertical | hlocal | hcorner
    · simp at hvertical
    · simp at hlocal
    · rcases hcorner with ⟨_, _, hpair, hne⟩
      change pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n) u = v at hpair
      change u ≠ v at hne
      simp only [parafermionicCoverFinitePairingForward]
      have hcorner := parafermionicCoverFiniteCutCorner_eq_corner_of_ne n hn hpair hne
      have hflip : parafermionicCoverIncomingPrimalLeft
          (parafermionicCoverFiniteCornerPairPerm n u).1 =
            !parafermionicCoverIncomingPrimalLeft u.1 := by
        simpa only [parafermionicCoverFiniteCornerPairPerm_val] using
          parafermionicCoverIncomingPrimalLeft_cornerPair u.1
      have hvflip : parafermionicCoverIncomingPrimalLeft v.1 =
          !parafermionicCoverIncomingPrimalLeft u.1 := by
        have hcornerVal : (parafermionicCoverFiniteCornerPairPerm n u).1 = v.1 :=
          congrArg Subtype.val hcorner
        rw [← hcornerVal]
        exact hflip
      by_cases hu : parafermionicCoverIncomingPrimalLeft u.1 = false
      · exact Or.inl ⟨hu, hpair, hne⟩
      · have hu' : parafermionicCoverIncomingPrimalLeft u.1 = true := by
          cases h' : parafermionicCoverIncomingPrimalLeft u.1 <;> simp_all
        have hv : parafermionicCoverIncomingPrimalLeft v.1 = false := by
          simpa [hu'] using hvflip
        have hrev : pairingSingleCutPerm
            (parafermionicCoverFiniteCornerPairPerm n)
            (parafermionicCoverFiniteOriginCornerPort n hn)
              (parafermionicCoverFiniteCornerPairPerm_involutive n) v = u := by
          rw [← hpair]
          change pairingSingleCut (parafermionicCoverFiniteCornerPairPerm n)
            (parafermionicCoverFiniteOriginCornerPort n hn)
            (pairingSingleCut (parafermionicCoverFiniteCornerPairPerm n)
              (parafermionicCoverFiniteOriginCornerPort n hn) u) = u
          exact pairingSingleCut_involutive
            (parafermionicCoverFiniteCornerPairPerm n)
            (parafermionicCoverFiniteOriginCornerPort n hn)
            (parafermionicCoverFiniteCornerPairPerm_involutive n) u
        exact Or.inr ⟨hv, hrev, hne.symm⟩

theorem parafermionicCoverFinitePairingForward_successor_unique (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huv : parafermionicCoverFinitePairingForward n hn A u v)
    (huw : parafermionicCoverFinitePairingForward n hn A u w) : v = w := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  rcases w with ⟨w, bw⟩
  cases bu <;> cases bv <;> cases bw <;>
    simp only [parafermionicCoverFinitePairingForward] at huv huw <;>
    simp_all <;> aesop

end
end PottsContinuity.FKC.FiniteFK
