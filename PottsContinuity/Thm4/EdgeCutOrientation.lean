/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutOrientation.lean`.
Adaptation: namespace/import relocation only.
-/
module

public import PottsContinuity.Thm4.EdgeCutPartner
public import PottsContinuity.Thm4.ExplorationOrientation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
open SimpleGraph
noncomputable section

local instance orientationPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance orientationCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

/-- The directed edges of the actual finite cut graph, oriented by the existing
primal-left pairing orientation. -/
def parafermionicCoverFiniteEdgeCutForward (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (u v : ParafermionicCoverFinitePort n × Bool) : Prop :=
  (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v ∧
    parafermionicCoverFinitePairingForward n hn A u v

theorem parafermionicCoverFiniteEdgeCut_adj_or_forward (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v) :
    parafermionicCoverFiniteEdgeCutForward n hn A e u v ∨
      parafermionicCoverFiniteEdgeCutForward n hn A e v u := by
  have hbase : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v :=
    (parafermionicCoverFiniteEdgeCutGraph_adj_iff n hn A e u v).mp h |>.1
  rcases parafermionicCoverFinitePairing_adj_or_forward n hn A hbase with huv | hvu
  · exact Or.inl ⟨h, huv⟩
  · exact Or.inr ⟨h.symm, hvu⟩

private theorem coverCutCorner_eq_corner_of_ne
    (n : ℕ) (hn : 1 ≤ n) {u v : ParafermionicCoverFinitePort n}
    (h : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) u = v)
    (hne : u ≠ v) : parafermionicCoverFiniteCornerPairPerm n u = v := by
  have hnot : ¬ (u = parafermionicCoverFiniteOriginCornerPort n hn ∨
      u = parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) := by
    intro hc
    have hfix : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n) u = u := by
      rcases hc with hs | hs
      · subst u
        simp [pairingSingleCutPerm_apply, pairingSingleCut]
      · subst u
        have hback := parafermionicCoverFiniteCornerPairPerm_involutive n
          (parafermionicCoverFiniteOriginCornerPort n hn)
        simp [pairingSingleCutPerm_apply, pairingSingleCut]
    exact hne (hfix.symm.trans h)
  simpa [pairingSingleCutPerm_apply, pairingSingleCut, hnot] using h

theorem parafermionicCoverFiniteEdgeCutForward_not_both (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (huv : parafermionicCoverFiniteEdgeCutForward n hn A e u v)
    (hvu : parafermionicCoverFiniteEdgeCutForward n hn A e v u) : False := by
  have huv := huv.2
  have hvu := hvu.2
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv <;>
    simp only [parafermionicCoverFinitePairingForward] at huv hvu
  · rcases huv with ⟨hu, hp⟩
    rcases hvu with ⟨hv, hp'⟩
    have hflip := parafermionicCoverIncomingPrimalLeft_localPair
      (parafermionicCoverConfigurationExtensionState n A) u.1
    have hval := congrArg (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft c.1) hp
    rw [parafermionicCoverFiniteLocalPairPerm_val] at hval
    have : parafermionicCoverIncomingPrimalLeft v.1 =
        !parafermionicCoverIncomingPrimalLeft u.1 := by
      rw [← hp]
      exact hflip
    simp [hu, hv] at this
  · rcases huv with ⟨hu, hp⟩
    rcases hvu with ⟨hv, hp'⟩
    have heq : u = v := hp
    subst v
    simp_all
  · rcases huv with ⟨hu, hp⟩
    rcases hvu with ⟨hv, hp'⟩
    have heq : u = v := hp'.symm
    subst v
    simp_all
  · rcases huv with ⟨hu, hp, hne⟩
    rcases hvu with ⟨hv, hp', hne'⟩
    have hcorner := coverCutCorner_eq_corner_of_ne n hn hp hne
    have hval := congrArg (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverIncomingPrimalLeft c.1) hcorner
    rw [parafermionicCoverFiniteCornerPairPerm_val] at hval
    have hflip := parafermionicCoverIncomingPrimalLeft_cornerPair u.1
    have hflag : parafermionicCoverIncomingPrimalLeft v.1 =
        !parafermionicCoverIncomingPrimalLeft u.1 := by
      exact hval.symm.trans (by simpa only [parafermionicCoverFiniteCornerPairPerm_val] using hflip)
    simp [hu, hv] at hflag

theorem parafermionicCoverFiniteEdgeCut_adj_exactly_one_direction
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v) :
    (parafermionicCoverFiniteEdgeCutForward n hn A e u v ∨
      parafermionicCoverFiniteEdgeCutForward n hn A e v u) ∧
      ¬ (parafermionicCoverFiniteEdgeCutForward n hn A e u v ∧
        parafermionicCoverFiniteEdgeCutForward n hn A e v u) := by
  refine ⟨parafermionicCoverFiniteEdgeCut_adj_or_forward n hn A e h, ?_⟩
  rintro ⟨huv, hvu⟩
  exact parafermionicCoverFiniteEdgeCutForward_not_both n hn A e huv hvu

theorem parafermionicCoverFiniteEdgeCutForward_successor_unique (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huv : parafermionicCoverFiniteEdgeCutForward n hn A e u v)
    (huw : parafermionicCoverFiniteEdgeCutForward n hn A e u w) : v = w := by
  exact parafermionicCoverFinitePairingForward_successor_unique n hn A huv.2 huw.2

private theorem coverOrientation_change
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

private theorem coverOrientation_predecessor_unique
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huw : parafermionicCoverFinitePairingForward n hn A u w)
    (hvw : parafermionicCoverFinitePairingForward n hn A v w) : u = v := by
  have h1 := coverOrientation_change n hn A huw
  have h2 := coverOrientation_change n hn A hvw
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

  · have h1 := coverOrientation_change n hn A huw
    have h2 := coverOrientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := coverOrientation_change n hn A huw
    have h2 := coverOrientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := coverOrientation_change n hn A huw
    have h2 := coverOrientation_change n hn A hvw
    simp only [parafermionicCoverFinitePairingForward] at huw hvw
    rcases huw with ⟨hu, _⟩
    rcases hvw with ⟨hv, _⟩
    have h1' : parafermionicCoverIncomingPrimalLeft w =
        parafermionicCoverIncomingPrimalLeft u := by simpa using h1
    have h2' : parafermionicCoverIncomingPrimalLeft w =
        !parafermionicCoverIncomingPrimalLeft v := by simpa using h2
    simp [hu, hv] at h1' h2'
    exact Bool.noConfusion (h1'.symm.trans h2')
  · have h1 := coverOrientation_change n hn A huw
    have h2 := coverOrientation_change n hn A hvw
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

theorem parafermionicCoverFiniteEdgeCutForward_predecessor_unique (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huw : parafermionicCoverFiniteEdgeCutForward n hn A e u w)
    (hvw : parafermionicCoverFiniteEdgeCutForward n hn A e v w) : u = v := by
  exact coverOrientation_predecessor_unique n hn A huw.2 hvw.2

/-- A source terminal is one whose layer agrees with the primal-left flag. -/
def parafermionicCoverFiniteEdgeCutSource (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e) : Prop :=
  v.1.2 = parafermionicCoverIncomingPrimalLeft v.1.1.1

private theorem coverEdgeCutTerminal_degree_one (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree v.1 = 1 := by
  have hmem : v.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
    rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
    exact v.2
  exact (Finset.mem_filter.mp hmem).2

theorem parafermionicCoverFiniteEdgeCutTerminal_adj_vertical (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e)
    {w : ParafermionicCoverFinitePort n × Bool}
    (hvw : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj v.1 w) :
    w.1 = v.1.1 ∧ w.2 ≠ v.1.2 := by
  have hz : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj v.1
      (v.1.1, !v.1.2) := by
    rcases v with ⟨⟨c, b⟩, hmem⟩
    cases b
    · exact (parafermionicCoverFiniteEdgeCutGraph_adj_false_true n hn A e c c).mpr rfl
    · exact (parafermionicCoverFiniteEdgeCutGraph_adj_true_false n hn A e c c).mpr rfl
  obtain ⟨x, hx, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp
    (coverEdgeCutTerminal_degree_one n hn A e v)
  have hzw : w = (v.1.1, !v.1.2) := (huniq w hvw).trans
    (huniq (v.1.1, !v.1.2) hz).symm
  subst w
  constructor
  · rfl
  · cases hb : v.val.2 <;> simp

theorem parafermionicCoverFiniteEdgeCutTerminal_forward_iff_source
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e)
    {w : ParafermionicCoverFinitePort n × Bool}
    (hvw : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj v.1 w) :
    parafermionicCoverFiniteEdgeCutForward n hn A e v.1 w ↔
      parafermionicCoverFiniteEdgeCutSource n hn e v := by
  have hvertical := parafermionicCoverFiniteEdgeCutTerminal_adj_vertical n hn A e v hvw
  cases hb : v.1.2 with
  | false =>
    cases hw : w.2 with
    | false =>
      exact False.elim (hvertical.2 (by rw [hw, hb]))
    | true =>
      have hport : v.1.1 = w.1 := hvertical.1.symm
      constructor
      · intro hdir
        have hfw : parafermionicCoverIncomingPrimalLeft v.1.1.1 = false ∧
            v.1.1 = w.1 := by
          simpa [parafermionicCoverFinitePairingForward, hb, hw] using hdir.2
        simpa [parafermionicCoverFiniteEdgeCutSource, hb] using hfw.1.symm
      · intro hsrc
        have hflag : parafermionicCoverIncomingPrimalLeft v.1.1.1 = false := by
          simpa [parafermionicCoverFiniteEdgeCutSource, hb] using hsrc.symm
        exact ⟨hvw, by
          simpa [parafermionicCoverFinitePairingForward, hb, hw] using
            (And.intro hflag hport)⟩
  | true =>
    cases hw : w.2 with
    | false =>
      have hport : v.1.1 = w.1 := hvertical.1.symm
      constructor
      · intro hdir
        have hfw : parafermionicCoverIncomingPrimalLeft v.1.1.1 = true ∧
            v.1.1 = w.1 := by
          simpa [parafermionicCoverFinitePairingForward, hb, hw] using hdir.2
        simpa [parafermionicCoverFiniteEdgeCutSource, hb] using hfw.1.symm
      · intro hsrc
        have hflag : parafermionicCoverIncomingPrimalLeft v.1.1.1 = true := by
          simpa [parafermionicCoverFiniteEdgeCutSource, hb] using hsrc.symm
        exact ⟨hvw, by
          simpa [parafermionicCoverFinitePairingForward, hb, hw] using
            (And.intro hflag hport)⟩
    | true =>
      exact False.elim (hvertical.2 (by rw [hw, hb]))

theorem parafermionicCoverFiniteEdgeCutTerminal_reverse_iff_not_source
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e)
    {w : ParafermionicCoverFinitePort n × Bool}
    (hvw : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj v.1 w) :
    parafermionicCoverFiniteEdgeCutForward n hn A e w v.1 ↔
      ¬ parafermionicCoverFiniteEdgeCutSource n hn e v := by
  have hexact := parafermionicCoverFiniteEdgeCut_adj_exactly_one_direction n hn A e hvw
  have hout := parafermionicCoverFiniteEdgeCutTerminal_forward_iff_source n hn A e v hvw
  constructor
  · intro hback hsource
    exact parafermionicCoverFiniteEdgeCutForward_not_both n hn A e
      (hout.mpr hsource) hback
  · intro hnot
    rcases hexact.1 with hout' | hback
    · exact False.elim (hnot (hout.mp hout'))
    · exact hback

end
end PottsContinuity.Thm4
