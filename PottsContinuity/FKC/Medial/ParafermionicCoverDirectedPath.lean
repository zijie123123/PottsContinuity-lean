-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverDirectedPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationOrientation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open LatticePort
noncomputable section

local instance coverDirectedPathAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

private theorem parafermionicCoverFinitePairingForward_orientation_change
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : parafermionicCoverFinitePairingForward n hn A u v) :
    parafermionicCoverIncomingPrimalLeft v.1 =
      if u.2 = v.2 then !parafermionicCoverIncomingPrimalLeft u.1
      else parafermionicCoverIncomingPrimalLeft u.1 := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv <;>
    simp only [parafermionicCoverFinitePairingForward] at h
  · rcases h with ⟨_, hp⟩
    have hval := congrArg (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft c.1) hp
    rw [parafermionicCoverFiniteLocalPairPerm_val] at hval
    have hflip := parafermionicCoverIncomingPrimalLeft_localPair
      (parafermionicCoverConfigurationExtensionState n A) u.1
    simpa using hval.symm.trans hflip
  · rcases h with ⟨_, hp⟩
    have hval := congrArg Subtype.val hp
    simpa using (congrArg parafermionicCoverIncomingPrimalLeft hval).symm
  · rcases h with ⟨_, hp⟩
    have hval := congrArg Subtype.val hp
    simpa using (congrArg parafermionicCoverIncomingPrimalLeft hval).symm
  · rcases h with ⟨_, hp, hpairne⟩
    have hcorner : parafermionicCoverFiniteCornerPairPerm n u = v := by
      have hc : ¬ (u = parafermionicCoverFiniteOriginCornerPort n hn ∨
          u = parafermionicCoverFiniteCornerPairPerm n
            (parafermionicCoverFiniteOriginCornerPort n hn)) := by
        intro hc
        have hfix : pairingSingleCutPerm
            (parafermionicCoverFiniteCornerPairPerm n)
            (parafermionicCoverFiniteOriginCornerPort n hn)
            (parafermionicCoverFiniteCornerPairPerm_involutive n) u = u := by
          rcases hc with hs | hs
          · subst u
            simp [pairingSingleCutPerm_apply, pairingSingleCut]
          · subst u
            have hback := parafermionicCoverFiniteCornerPairPerm_involutive n
              (parafermionicCoverFiniteOriginCornerPort n hn)
            simp [pairingSingleCutPerm_apply, pairingSingleCut]
        exact hpairne (hfix.symm.trans hp)
      simpa [pairingSingleCutPerm_apply, pairingSingleCut, hc] using hp
    have hval := congrArg (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft c.1) hcorner
    rw [parafermionicCoverFiniteCornerPairPerm_val] at hval
    have hflip := parafermionicCoverIncomingPrimalLeft_cornerPair u.1
    simpa using hval.symm.trans hflip

private theorem parafermionicCoverFinitePairingForward_predecessor_unique
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huw : parafermionicCoverFinitePairingForward n hn A u w)
    (hvw : parafermionicCoverFinitePairingForward n hn A v w) : u = v := by
  have h1 := parafermionicCoverFinitePairingForward_orientation_change n hn A huw
  have h2 := parafermionicCoverFinitePairingForward_orientation_change n hn A hvw
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  rcases w with ⟨w, bw⟩
  cases bu <;> cases bv <;> cases bw
  · simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨_, hU⟩
    rcases hvw with ⟨_, hV⟩
    have hs := Function.Involutive.injective
      (parafermionicCoverFiniteLocalPairPerm_involutive n A) (hU.trans hV.symm)
    cases hs
    rfl

  · simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨_, hU⟩
    rcases hvw with ⟨_, hV⟩
    have hs : u = v := hU.trans hV.symm
    cases hs
    rfl

  · have h1 := parafermionicCoverFinitePairingForward_orientation_change n hn A huw
    have h2 := parafermionicCoverFinitePairingForward_orientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := parafermionicCoverFinitePairingForward_orientation_change n hn A huw
    have h2 := parafermionicCoverFinitePairingForward_orientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := parafermionicCoverFinitePairingForward_orientation_change n hn A huw
    have h2 := parafermionicCoverFinitePairingForward_orientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := parafermionicCoverFinitePairingForward_orientation_change n hn A huw
    have h2 := parafermionicCoverFinitePairingForward_orientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _, _⟩
    rcases hvw with ⟨hv, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨_, hU⟩
    rcases hvw with ⟨_, hV⟩
    have hs : u = v := hU.trans hV.symm
    cases hs
    rfl
  · simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨_, hU, _⟩
    rcases hvw with ⟨_, hV, _⟩
    have hs := Function.Involutive.injective
      (pairingSingleCut_involutive
        (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n)) (hU.trans hV.symm)
    cases hs
    rfl

 def parafermionicCoverFiniteWalkForward (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    {u v : ParafermionicCoverFinitePort n × Bool} →
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v → Prop
    | _, _, .nil => True
    | _, _, .cons (u := u) (v := v) _ p =>
        parafermionicCoverFinitePairingForward n hn A u v ∧
          parafermionicCoverFiniteWalkForward n hn A p

private theorem parafermionicCoverFiniteWalkForward_of_incoming
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {a b t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk b t)
    (hp : p.IsPath)
    (hab : parafermionicCoverFinitePairingForward n hn A a b)
    (ha : a ∉ p.support) : parafermionicCoverFiniteWalkForward n hn A p := by
  revert a hab ha hp
  induction p with
  | nil =>
      intro a hp hab ha
      trivial
  | @cons b c t hbc tail ih =>
      intro a hp hab ha
      have hbcForward : parafermionicCoverFinitePairingForward n hn A b c := by
        rcases parafermionicCoverFinitePairing_adj_or_forward n hn A hbc with h | h
        · exact h
        · have hac := parafermionicCoverFinitePairingForward_predecessor_unique
            n hn A hab h
          have hc : c ∈ (SimpleGraph.Walk.cons hbc tail).support := by
            simp [SimpleGraph.Walk.support_cons]
          exact (ha (hac.symm ▸ hc)).elim
      have hbNotTail : b ∉ tail.support := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact ⟨hbcForward,
        ih (SimpleGraph.Walk.IsPath.of_cons hp) hbcForward hbNotTail⟩

private theorem parafermionicCoverFiniteOrigin_no_incoming (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    ∀ u, ¬ parafermionicCoverFinitePairingForward n hn A u
      ((parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  intro u hu
  rcases u with ⟨u, bu⟩
  cases bu
  · simp only [parafermionicCoverFinitePairingForward] at hu
    rcases hu with ⟨hor, huv⟩
    have hval := congrArg Subtype.val huv
    rw [parafermionicCoverFiniteOriginCornerPort_val] at hval
    subst u
    have : parafermionicCoverIncomingPrimalLeft
        parafermionicCoverOriginCornerPort = false := hor
    rw [parafermionicCoverIncomingPrimalLeft_origin] at this
    cases this
  · simp only [parafermionicCoverFinitePairingForward] at hu
    rcases hu with ⟨hor, hpair, hne⟩
    have hfix : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n)
        (parafermionicCoverFiniteOriginCornerPort n hn) =
          parafermionicCoverFiniteOriginCornerPort n hn := by
      simp [pairingSingleCutPerm_apply, pairingSingleCut]
    have hval := Function.Involutive.injective
      (pairingSingleCut_involutive (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n))
        (by simpa only [pairingSingleCutPerm_apply] using hpair.trans hfix.symm)
    subst u
    exact hne rfl

private theorem parafermionicCoverFiniteWalkForward_of_no_incoming
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {s t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk s t)
    (hp : p.IsPath)
    (hsource : ∀ u, ¬ parafermionicCoverFinitePairingForward n hn A u s) :
    parafermionicCoverFiniteWalkForward n hn A p := by
  cases p with
  | nil => trivial
  | cons hxy tail =>
      rename_i c
      have hxyForward : parafermionicCoverFinitePairingForward n hn A s c := by
        rcases parafermionicCoverFinitePairing_adj_or_forward n hn A hxy with h | h
        · exact h
        · exact (hsource c h).elim
      have htailPath := SimpleGraph.Walk.IsPath.of_cons hp
      have hxNotTail : s ∉ tail.support := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact ⟨hxyForward,
        parafermionicCoverFiniteWalkForward_of_incoming n hn A tail htailPath
          hxyForward hxNotTail⟩

private theorem parafermionicCoverFiniteWalkForward_darts
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hp : parafermionicCoverFiniteWalkForward n hn A p) :
    ∀ d ∈ p.darts,
      parafermionicCoverFinitePairingForward n hn A d.fst d.snd := by
  induction p with
  | nil => intro d hd; simp at hd
  | @cons u v w huv tail ih =>
      intro d hd
      rcases hp with ⟨hforward, htail⟩
      simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with hd | hd
      · cases hd
        exact hforward
      · exact ih htail d hd

theorem parafermionicCoverFiniteCornerCut_isPath_forward (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    ∀ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      parafermionicCoverFinitePairingForward n hn A d.fst d.snd := by
  apply parafermionicCoverFiniteWalkForward_darts n hn A
  exact parafermionicCoverFiniteWalkForward_of_no_incoming n hn A _
    (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A)
    (parafermionicCoverFiniteOrigin_no_incoming n hn A)

end
end PottsContinuity.FKC.FiniteFK
