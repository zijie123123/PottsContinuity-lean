-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutRoutingWalk.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutPathSystem
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutReconnection
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutReconnectionTurn
public import PottsContinuity.FKC.Medial.ThreeTerminalRouting
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance routingWalkPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance routingWalkCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

local instance routingWalkCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj := Classical.decRel _

def parafermionicCoverFiniteEdgeCutRoutingSuccessor (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) : Equiv.Perm ThreeTerminal :=
  if e ∈ A then openRoutingSuccessor
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e)
  else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e

def parafermionicCoverFiniteEdgeCutRoutingLength (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) : ℕ :=
  firstPositiveReturnLength (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e)

 theorem edgeCutGraph_le_cornerCut (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn A := by
  intro u v huv
  exact huv.1

def parafermionicCoverFiniteEdgeCutSourcePath_cornerCut (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath n hn A e i
  exact (p.mapLe (edgeCutGraph_le_cornerCut n hn A e)).copy (by
    simp [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv] ) (by
    simpa [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv,
      parafermionicCoverFiniteEdgeCutSinkLabelsEquiv] using
      parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e i)

theorem parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).IsPath := by
  change (((parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).mapLe
    (edgeCutGraph_le_cornerCut n hn A e)).copy (by
      simp [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv]) (by
      simpa [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv,
        parafermionicCoverFiniteEdgeCutSinkLabelsEquiv] using
        parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e i)).IsPath
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy]
  exact (parafermionicCoverFiniteEdgeCutSourcePath_isPath n hn A e i).mapLe
    (edgeCutGraph_le_cornerCut n hn A e) |>.support_nodup

theorem parafermionicCoverFiniteEdgeCutRoutingAdj
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i ≠ 0) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i)).1.1 := by
  have hj : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i ≠ 0 := by
    intro hz
    apply hi
    by_cases he : e ∈ A
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply, threeTerminalSwap_zero, hz]
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he, hz]
  have hturn := parafermionicCoverFiniteEdgeCutRestoredSinkEdge_forward_turn
    n hn A e (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) hj
  have htarget : (if e ∈ A then
      threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)
    else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) =
      parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i := by
    by_cases he : e ∈ A
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply]
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he]
  rw [← htarget]
  exact hturn.1

theorem parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) {i j : ThreeTerminal} (hij : i ≠ j) :
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support.Disjoint
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j).support := by
  simpa [parafermionicCoverFiniteEdgeCutSourcePath_cornerCut, SimpleGraph.Walk.support_copy] using
    parafermionicCoverFiniteEdgeCutSourcePath_support_disjoint n hn A e hij

private theorem splice_isPath
    {V : Type*} {G : SimpleGraph V} [DecidableEq V] {s u v t : V}
    (p : G.Walk s u) (q : G.Walk v t) (hp : p.IsPath) (hq : q.IsPath)
    (hadj : G.Adj u v) (hdisj : p.support.Disjoint q.support) :
    (p.append (SimpleGraph.Walk.cons hadj q)).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  simpa using List.Nodup.append hp.support_nodup hq.support_nodup hdisj

theorem parafermionicCoverFiniteEdgeCutSourceLabel_zero_point (n : ℕ) (hn : 1 ≤ n)
    (_A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0).1.1 =
      (parafermionicCoverFiniteOriginCornerPort n hn, true) := by
  simp [parafermionicCoverFiniteEdgeCutSourceLabels_zero,
    parafermionicCoverFiniteEdgeCutSourceCorner]

theorem parafermionicCoverFiniteEdgeCutSinkLabel_zero_point (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (i : ThreeTerminal)
    (hp : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 =
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  rw [hp, parafermionicCoverFiniteEdgeCutSinkLabels_zero]
  simp [parafermionicCoverFiniteEdgeCutSinkCorner]

def parafermionicCoverFiniteEdgeCutRoutingSplice
    {V : Type*} {G : SimpleGraph V} {s u v t : V}
    (p : G.Walk s u) (q : G.Walk v t) (hadj : G.Adj u v) : G.Walk s t :=
  p.append (SimpleGraph.Walk.cons hadj q)

theorem parafermionicCoverFiniteEdgeCutRoutingSplice_isPath
    {V : Type*} {G : SimpleGraph V} [DecidableEq V] {s u v t : V}
    (p : G.Walk s u) (q : G.Walk v t) (hp : p.IsPath) (hq : q.IsPath)
    (hadj : G.Adj u v) (hdisj : p.support.Disjoint q.support) :
    (parafermionicCoverFiniteEdgeCutRoutingSplice p q hadj).IsPath := by
  exact splice_isPath p q hp hq hadj hdisj

theorem parafermionicCoverFiniteEdgeCutRoutingSplice_support
    {V : Type*} {G : SimpleGraph V} {s u v t : V}
    (p : G.Walk s u) (q : G.Walk v t) (hadj : G.Adj u v) :
    (parafermionicCoverFiniteEdgeCutRoutingSplice p q hadj).support = p.support ++ q.support := by
  simp [parafermionicCoverFiniteEdgeCutRoutingSplice, SimpleGraph.Walk.support_append]

private theorem source_disjoint_join (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i j k : ThreeTerminal)
    (hij : i ≠ j) (hik : i ≠ k) (hadj :
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e j)).1.1
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e k).1.1) :
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).support.Disjoint
      (parafermionicCoverFiniteEdgeCutRoutingSplice (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j)
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e k) hadj).support := by
  rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
  apply List.disjoint_left.mpr
  intro x hxi hxjk
  simp only [List.mem_append] at hxjk
  rcases hxjk with hxj | hxk
  · exact (List.disjoint_left.mp
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne n hn A e hij)) hxi hxj
  · exact (List.disjoint_left.mp
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne n hn A e hik)) hxi hxk

private theorem routingWalk_eq_originExploration
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (w : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true))
    (hw : w.IsPath) :
    w = parafermionicCoverFiniteOriginExplorationPath n hn A := by
  let huniq := parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn A
  exact huniq.unique hw huniq.choose_spec.1

theorem parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (h : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = 0) :
    parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0 := by
  by_cases he : e ∈ A
  · have hs : threeTerminalSwap
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) = 0 := by
      simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply] using h
    exact threeTerminalSwap.injective (by simpa [threeTerminalSwap_zero] using hs)
  · simpa [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using h

theorem parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return
    (r : Equiv.Perm ThreeTerminal) (h0 : r 0 ≠ 0) (h1 : r (r 0) ≠ 0) :
    r (r (r 0)) = 0 := by
  have hreturn := firstPositiveReturnLength_returns r
  have hlen : firstPositiveReturnLength r = 3 := by
    simp [firstPositiveReturnLength, h0, h1]
  rw [hlen] at hreturn
  simpa [Function.iterate_succ_apply'] using hreturn

private theorem parafermionicCoverFiniteEdgeCutRoutingSplice_copy_isPath
    {V : Type*} {G : SimpleGraph V} [DecidableEq V] {s u v t s' t' : V}
    (p : G.Walk s u) (q : G.Walk v t) (hp : p.IsPath) (hq : q.IsPath)
    (hadj : G.Adj u v) (hdisj : p.support.Disjoint q.support)
    (hs : s = s') (ht : t = t') :
    ((parafermionicCoverFiniteEdgeCutRoutingSplice p q hadj).copy hs ht).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy]
  exact (parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p q hp hq hadj hdisj).support_nodup

private theorem walk_copy_isPath
    {V : Type*} {G : SimpleGraph V} [DecidableEq V] {s t s' t' : V}
    (p : G.Walk s t) (hp : p.IsPath) (hs : s = s') (ht : t = t') :
    (p.copy hs ht).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy]
  exact hp.support_nodup

/-- Following the actual terminal permutation and restoring each traversed
edge reconstructs the unique corner-cut exploration. -/
theorem parafermionicCoverFiniteEdgeCutRoutingWalk_exists
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∃ w : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true),
      w.IsPath ∧ w = parafermionicCoverFiniteOriginExplorationPath n hn A := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let P := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e
  by_cases h0 : r 0 = 0
  · have hp0 : π 0 = 0 := parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e 0 h0
    let q := P 0
    let w := q.copy (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
      (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e 0 (by simpa [π] using hp0))
    refine ⟨w, ?_, ?_⟩
    · exact walk_copy_isPath q (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0) _ _
    · exact routingWalk_eq_originExploration n hn A w
        (walk_copy_isPath q (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0) _ _)
  · let i := r 0
    by_cases h1 : r i = 0
    · have hpLast : π i = 0 :=
        parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i h1
      let p0 := P 0
      let p1 := P i
      have hadj := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 (by simpa [i] using h0)
      let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 p1 hadj
      let w := route.copy (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
        (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e i (by simpa [π] using hpLast))
      have hdisj : p0.support.Disjoint p1.support := by
        exact parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne n hn A e (by
          intro h
          exact h0 (by simpa [i] using h.symm))
      have hroute : route.IsPath := parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p0 p1
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0)
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e i) hadj hdisj
      refine ⟨w, ?_, ?_⟩
      · exact walk_copy_isPath route hroute _ _
      · exact routingWalk_eq_originExploration n hn A w
          (walk_copy_isPath route hroute _ _)

    · have hreturn := firstPositiveReturnLength_returns r
      have h2 : r (r i) = 0 := by
        have hlen : firstPositiveReturnLength r = 3 := by
          simp [firstPositiveReturnLength, h0, h1, i]
        rw [hlen] at hreturn
        simpa [Function.iterate_succ_apply', i] using hreturn
      let j := r i
      have hpLast : π j = 0 :=
        parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j (by simpa [j] using h2)
      let p0 := P 0
      let p1 := P i
      let p2 := P j
      have hadj01 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 (by simpa [i] using h0)
      have hadj12 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i (by simpa [j] using h1)
      let inner := parafermionicCoverFiniteEdgeCutRoutingSplice p1 p2 hadj12
      let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 inner hadj01
      let w := route.copy (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
        (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j (by simpa [π] using hpLast))
      have hii : i ≠ 0 := by simpa [i] using h0
      have hij : i ≠ j := by
        intro hh
        have hfix : r i = i := by simpa [j] using hh.symm
        have hfix0 : r (r 0) = r 0 := by simpa [i] using hfix
        exact h0 (r.injective hfix0)
      have h0j : (0 : ThreeTerminal) ≠ j := by
        simpa [j] using Ne.symm h1
      have hdisj12 : p1.support.Disjoint p2.support :=
        parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne n hn A e (by simpa [p1, p2] using hij)
      have hinner : inner.IsPath := parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p1 p2
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e i)
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e j) hadj12 hdisj12
      have hdisj : p0.support.Disjoint inner.support := by
        exact source_disjoint_join n hn A e 0 i j (Ne.symm hii) h0j hadj12
      have hroute : route.IsPath := parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p0 inner
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0) hinner hadj01 hdisj
      have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
      have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j
        (by simpa [π] using hpLast)
      refine ⟨w, ?_, ?_⟩
      · exact walk_copy_isPath route hroute hs ht
      · exact routingWalk_eq_originExploration n hn A w
          (walk_copy_isPath route hroute hs ht)

/-- The canonical reconstructed walk, chosen from the explicit three-case
concatenation existence proof above. -/
noncomputable def parafermionicCoverFiniteEdgeCutRoutingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) :=
  Classical.choose (parafermionicCoverFiniteEdgeCutRoutingWalk_exists n hn A e)

theorem parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutRoutingWalk n hn A e =
      parafermionicCoverFiniteOriginExplorationPath n hn A :=
  (Classical.choose_spec (parafermionicCoverFiniteEdgeCutRoutingWalk_exists n hn A e)).2

theorem parafermionicCoverFiniteEdgeCutRoutingWalk_twoSegments
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    parafermionicCoverFiniteEdgeCutRoutingWalk n hn A e =
      (parafermionicCoverFiniteEdgeCutRoutingSplice
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0)
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0))
        (parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0)).copy
        (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
        (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0)
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e
            (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) h1)) := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let p0 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0
  let p1 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  have hpLast : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i
      (by simpa [i] using h1)
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e i hpLast
  let candidate := (parafermionicCoverFiniteEdgeCutRoutingSplice p0 p1
    (parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0)).copy
    hs ht
  have hdisj : p0.support.Disjoint p1.support :=
    parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
      n hn A e (by
        intro hh
        exact h0 (by simpa [i] using hh.symm))
  have hpath := parafermionicCoverFiniteEdgeCutRoutingSplice_copy_isPath p0 p1
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0)
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e i)
    (parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0) hdisj hs ht
  simpa [candidate, p0, p1, i, r] using
    (parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e).trans
      (routingWalk_eq_originExploration n hn A candidate hpath).symm

theorem parafermionicCoverFiniteEdgeCutRoutingWalk_threeSegments
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let i := r 0
    let j := r i
    parafermionicCoverFiniteEdgeCutRoutingWalk n hn A e =
      (parafermionicCoverFiniteEdgeCutRoutingSplice
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0)
        (parafermionicCoverFiniteEdgeCutRoutingSplice
          (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i)
          (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j)
          (parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i h1))
        (parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0)).copy
        (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
        (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j
          (parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j
            (by
              have hret := parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return
                (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e) h0 h1
              simpa [j, i] using hret))) := by
  dsimp
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let j := r i
  let p0 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0
  let p1 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  let p2 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j
  let hadj01 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0
  let hadj12 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i h1
  let inner := parafermionicCoverFiniteEdgeCutRoutingSplice p1 p2 hadj12
  let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 inner hadj01
  have hlast := parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return r h0 h1
  let candidate := route.copy
    (parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e)
    (parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j
        (by simpa [j, i] using hlast)))
  have hij : i ≠ j := by
    intro hh
    have hfix : r i = i := by simpa [j] using hh.symm
    have hfix0 : r (r 0) = r 0 := by simpa [i] using hfix
    exact h0 (r.injective hfix0)
  have h0j : (0 : ThreeTerminal) ≠ j := by simpa [j] using Ne.symm h1
  have hdisj12 : p1.support.Disjoint p2.support :=
    parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
      n hn A e (by simpa [p1, p2] using hij)
  have hinner := parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p1 p2
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e i)
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e j)
    hadj12 hdisj12
  have hdisj : p0.support.Disjoint inner.support :=
    source_disjoint_join n hn A e 0 i j (by simpa [i] using Ne.symm h0) h0j hadj12
  have hroute := parafermionicCoverFiniteEdgeCutRoutingSplice_isPath p0 inner
    (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_isPath n hn A e 0)
    hinner hadj01 hdisj
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j
    (parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j
      (by simpa [j, i] using hlast))
  have hpath := walk_copy_isPath route hroute hs ht
  simpa [candidate, route, inner, p0, p1, p2, hadj01, hadj12, r, i, j] using
    (parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e).trans
      (routingWalk_eq_originExploration n hn A candidate hpath).symm
end
end PottsContinuity.FKC.FiniteFK
