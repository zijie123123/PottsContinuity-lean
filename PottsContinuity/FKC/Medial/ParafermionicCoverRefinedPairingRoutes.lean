-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPairingRoutes.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationOrientation
public import PottsContinuity.FKC.Medial.ParafermionicCoverFinitePorts
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCapPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerPath
public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK

abbrev parafermionicCoverRefinedPairingEmbedding {n : ℕ}
    (u : ParafermionicCoverFinitePort n × Bool) :
    ParafermionicCoverVertex :=
  parafermionicCoverRefinedPortEmbedding (u.1.1, u.2)

theorem parafermionicCoverRefinedPairingEmbedding_injective (n : ℕ) :
    Function.Injective (@parafermionicCoverRefinedPairingEmbedding n) := by
  intro u v h
  have heq : (u.1.1, u.2) = (v.1.1, v.2) :=
    parafermionicCoverRefinedPortEmbedding_injective h
  have hport : u.1 = v.1 := Subtype.ext (congrArg Prod.fst heq)
  have hbool : u.2 = v.2 := congrArg (fun z : ParafermionicCoverPort × Bool => z.2) heq
  exact Prod.ext hport hbool

/-- The exact ordered support assigned to an actual corner-cut pairing edge by
the refined embedding. Open local pairs use their one-edge route, closed pairs
use the named cap midpoint, and surviving corner pairs use the named four-edge
corner path. -/
noncomputable def parafermionicCoverRefinedPairingRouteSupport (n : ℕ) (_hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) : List ParafermionicCoverVertex :=
  match u.2, v.2 with
  | false, false =>
      if parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) u.1.1 then
        [parafermionicCoverRefinedPairingEmbedding u,
          parafermionicCoverRefinedPairingEmbedding v]
      else
        [parafermionicCoverRefinedPairingEmbedding u,
          parafermionicCoverRefinedClosedCapMiddle u.1.1,
          parafermionicCoverRefinedPairingEmbedding v]
  | true, true =>
      [parafermionicCoverRefinedPairingEmbedding u,
        parafermionicCoverRefinedCornerMid₁ u.1.1,
        parafermionicCoverRefinedCornerElbow u.1.1,
        parafermionicCoverRefinedCornerMid₂ u.1.1,
        parafermionicCoverRefinedPairingEmbedding v]
  | _, _ => [parafermionicCoverRefinedPairingEmbedding u,
      parafermionicCoverRefinedPairingEmbedding v]

private theorem refinedPairingCopy_isPath {G : SimpleGraph ParafermionicCoverVertex}
    {u v u' v' : ParafermionicCoverVertex} (p : G.Walk u v) (hp : p.IsPath)
    (hu : u = u') (hv : v = v') : (p.copy hu hv).IsPath := by
  rw [Walk.isPath_def, Walk.support_copy]
  exact (Walk.isPath_def _).mp hp

 theorem refinedPairingRoute_exists (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    ∃ q : parafermionicCoverGraph.Walk (parafermionicCoverRefinedPairingEmbedding u)
      (parafermionicCoverRefinedPairingEmbedding v),
      q.IsPath ∧ q.support = parafermionicCoverRefinedPairingRouteSupport n hn A u v := by
  classical
  rcases u with ⟨c, b⟩
  rcases v with ⟨d, b'⟩
  have h' := (parafermionicCoverFiniteCornerCutPairingGraph_adj_iff n hn A
    (c, b) (d, b')).mp h
  cases b <;> cases b'
  · have hpair : parafermionicCoverFiniteLocalPairPerm n A c = d := by
      simp only [Bool.false_eq_true, false_and, and_false,
        or_false, true_and] at h'
      rcases h' with hlayer | hlocal
      · exact False.elim (hlayer.2 rfl)
      · exact hlocal.1
    have hraw : parafermionicCoverLocalPair
        (parafermionicCoverConfigurationExtensionState n A) c.1 = d.1 := by
      simpa only [parafermionicCoverFiniteLocalPairPerm_val] using
        congrArg Subtype.val hpair
    let ω : ParafermionicCoverConfiguration :=
      parafermionicCoverConfigurationExtensionState n A
    by_cases hs : parafermionicCoverPortBondState ω c.1
    · have hopen : parafermionicCoverOpenPair c.1 = d.1 := by
        simpa only [parafermionicCoverLocalPair, ω, ite_eq_left hs] using hraw
      have hs' : parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) c.1 = true := by
        change parafermionicCoverPortBondState ω c.1 = true
        exact hs
      let q := (Walk.cons (parafermionicCoverRefinedPortEmbedding_openPair_adj c.1)
        Walk.nil).copy rfl (congrArg (fun x =>
          parafermionicCoverRefinedPortEmbedding (x, false)) hopen)
      refine ⟨q, ?_, ?_⟩
      have hpath : (Walk.cons (parafermionicCoverRefinedPortEmbedding_openPair_adj c.1)
          Walk.nil).IsPath := by
        apply (Walk.cons_isPath_iff _ _).2
        refine ⟨Walk.IsPath.nil, ?_⟩
        have hne : parafermionicCoverRefinedPortEmbedding (c.1, false) ≠
            parafermionicCoverRefinedPortEmbedding (parafermionicCoverOpenPair c.1, false) := by
          intro he
          have he' := parafermionicCoverRefinedPortEmbedding_injective he
          exact (parafermionicCoverOpenPair_ne c.1).symm (congrArg Prod.fst he')
        simpa using hne
      · exact refinedPairingCopy_isPath _ hpath rfl _
      · have hcopy : q.support =
            (Walk.cons (parafermionicCoverRefinedPortEmbedding_openPair_adj c.1)
              Walk.nil).support :=
          Walk.support_copy _ rfl _
        rw [hcopy]
        simp [parafermionicCoverRefinedPairingRouteSupport,
          parafermionicCoverRefinedPairingEmbedding, hs', hopen]
    · have hclosed : parafermionicCoverClosedPair c.1 = d.1 := by
        simpa only [parafermionicCoverLocalPair, ω, ite_eq_right hs] using hraw
      have hs' : ¬ parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) c.1 = true := by
        change ¬ parafermionicCoverPortBondState ω c.1 = true
        exact hs
      let q := (parafermionicCoverRefinedClosedCapWalk c.1).copy rfl
        (congrArg (fun x => parafermionicCoverRefinedPortEmbedding (x, false)) hclosed)
      refine ⟨q, ?_, ?_⟩
      · exact refinedPairingCopy_isPath _
          (parafermionicCoverRefinedClosedCapWalk_isPath c.1) rfl _
      · have hcopy : q.support = (parafermionicCoverRefinedClosedCapWalk c.1).support :=
          Walk.support_copy _ rfl _
        rw [hcopy]
        simp [parafermionicCoverRefinedPairingRouteSupport,
          parafermionicCoverRefinedPairingEmbedding, hs', hclosed,
          parafermionicCoverRefinedClosedCapWalk_support]
  · have hport : c = d := by
      simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
        or_false, true_and] at h'
      exact h'.1
    have hadj : parafermionicCoverGraph.Adj
        (parafermionicCoverRefinedPortEmbedding (c.1, false))
        (parafermionicCoverRefinedPortEmbedding (c.1, true)) :=
      parafermionicCoverRefinedPortEmbedding_layer_adj c.1
    let q := (Walk.cons hadj Walk.nil).copy rfl
      (congrArg (fun x => parafermionicCoverRefinedPairingEmbedding (x, true)) hport)
    refine ⟨q, ?_, ?_⟩
    have hpath : (Walk.cons hadj Walk.nil).IsPath := by
      apply (Walk.cons_isPath_iff _ _).2
      refine ⟨Walk.IsPath.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton]
      intro he
      have he' := parafermionicCoverRefinedPortEmbedding_injective he
      exact Bool.noConfusion (congrArg Prod.snd he')
    · exact refinedPairingCopy_isPath _ hpath rfl _
    · have hcopy : q.support = (Walk.cons hadj Walk.nil).support :=
        Walk.support_copy _ rfl _
      rw [hcopy]
      simp [parafermionicCoverRefinedPairingRouteSupport, hport,
        parafermionicCoverRefinedPairingEmbedding]
  · have hport : c = d := by
      simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
        or_false, true_and] at h'
      exact h'.1
    have hadj : parafermionicCoverGraph.Adj
        (parafermionicCoverRefinedPortEmbedding (c.1, true))
        (parafermionicCoverRefinedPortEmbedding (c.1, false)) :=
      (parafermionicCoverRefinedPortEmbedding_layer_adj c.1).symm
    let q := (Walk.cons hadj Walk.nil).copy rfl
      (congrArg (fun x => parafermionicCoverRefinedPairingEmbedding (x, false)) hport)
    refine ⟨q, ?_, ?_⟩
    have hpath : (Walk.cons hadj Walk.nil).IsPath := by
      apply (Walk.cons_isPath_iff _ _).2
      refine ⟨Walk.IsPath.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton]
      intro he
      have he' := parafermionicCoverRefinedPortEmbedding_injective he
      exact Bool.noConfusion (congrArg Prod.snd he')
    · exact refinedPairingCopy_isPath _ hpath rfl _
    · have hcopy : q.support = (Walk.cons hadj Walk.nil).support :=
        Walk.support_copy _ rfl _
      rw [hcopy]
      simp [parafermionicCoverRefinedPairingRouteSupport, hport,
        parafermionicCoverRefinedPairingEmbedding]
  · have hpair :
        pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
          (parafermionicCoverFiniteOriginCornerPort n hn)
          (parafermionicCoverFiniteCornerPairPerm_involutive n) c = d := by
      simp only [Bool.true_eq_false, false_and, and_false,
        false_or, true_and] at h'
      rcases h' with hbad | hgood
      · exact False.elim (hbad.2 rfl)
      · exact hgood.1
    have hne : c ≠ d := by
      simp only [Bool.true_eq_false, false_and, and_false,
        false_or, true_and] at h'
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
    have hcorner : parafermionicCoverFiniteCornerPairPerm n c = d :=
      hcut.symm.trans hpair
    have hcornerRaw : parafermionicCoverCornerPair c.1 = d.1 := by
      simpa only [parafermionicCoverFiniteCornerPairPerm_val] using
        congrArg Subtype.val hcorner
    let q := (parafermionicCoverRefinedCornerWalk c.1).copy rfl
      (congrArg (fun x => parafermionicCoverRefinedPortEmbedding (x, true)) hcornerRaw)
    refine ⟨q, ?_, ?_⟩
    · exact refinedPairingCopy_isPath _
        (parafermionicCoverRefinedCornerWalk_isPath c.1) rfl _
    · have hcopy : q.support = (parafermionicCoverRefinedCornerWalk c.1).support :=
        Walk.support_copy _ rfl _
      rw [hcopy]
      simp [parafermionicCoverRefinedPairingRouteSupport, hcornerRaw,
        parafermionicCoverRefinedPairingEmbedding,
        parafermionicCoverRefinedCornerWalk_support]

noncomputable def parafermionicCoverRefinedPairingRoute (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    parafermionicCoverGraph.Walk (parafermionicCoverRefinedPairingEmbedding u)
      (parafermionicCoverRefinedPairingEmbedding v) :=
  Classical.choose (refinedPairingRoute_exists n hn A h)

theorem parafermionicCoverRefinedPairingRoute_isPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    (parafermionicCoverRefinedPairingRoute n hn A h).IsPath :=
  (Classical.choose_spec (refinedPairingRoute_exists n hn A h)).1

theorem parafermionicCoverRefinedPairingRoute_support (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    (parafermionicCoverRefinedPairingRoute n hn A h).support =
      parafermionicCoverRefinedPairingRouteSupport n hn A u v :=
  (Classical.choose_spec (refinedPairingRoute_exists n hn A h)).2

end PottsContinuity.FKC.Medial
