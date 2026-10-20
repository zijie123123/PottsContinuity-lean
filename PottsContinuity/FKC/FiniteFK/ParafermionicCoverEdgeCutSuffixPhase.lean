-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverEdgeCutSuffixPhase.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhase
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial SimpleGraph
noncomputable section

private theorem dropUntil_append_cons_of_notin_left
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s u v t w : V} (p : G.Walk s u) (q : G.Walk v t)
    (hadj : G.Adj u v) (hw : w ∈ q.support) (hnot : w ∉ p.support) :
    (p.append (Walk.cons hadj q)).dropUntil w
      (by simp [Walk.support_append, hnot, hw]) = q.dropUntil w hw := by
  revert hw hnot
  induction p with
  | nil =>
      intro hw hnot
      simp only [Walk.support_nil, List.mem_singleton] at hnot
      simp [Walk.append, Walk.dropUntil, hnot, eq_comm]
  | @cons a b c h p ih =>
      intro hw hnot
      have hne : a ≠ w := by
        intro heq
        exact hnot (by simp [heq])
      have hnotTail : w ∉ p.support := by
        intro hwTail
        exact hnot (by simp [hwTail])
      simp only [Walk.append]
      simpa [Walk.dropUntil, hne] using ih hadj hw hnotTail

private theorem dropUntil_append_cons_start
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s u v t : V} (p : G.Walk s u) (q : G.Walk v t)
    (hadj : G.Adj u v) (hnot : v ∉ p.support) :
    (p.append (Walk.cons hadj q)).dropUntil v
      (by simp [Walk.support_append, hnot]) = q := by
  simpa using dropUntil_append_cons_of_notin_left p q hadj q.start_mem_support hnot

private theorem pairingWalkTurn_copy_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v u' v' : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hu : u = u') (hv : v = v') :
    parafermionicCoverFinitePairingWalkTurn n hn A (p.copy hu hv) =
      parafermionicCoverFinitePairingWalkTurn n hn A p := by
  simp [parafermionicCoverFinitePairingWalkTurn, Walk.darts_copy]

private theorem dropUntil_eq_of_walk_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t z : V} {p q : G.Walk s t} (hpq : p = q)
    (hp : z ∈ p.support) (hq : z ∈ q.support) :
    p.dropUntil z hp = q.dropUntil z hq := by
  subst q
  rfl

private theorem pairingWalkTurn_splice
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {s u v t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk s u)
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk v t)
    (hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutRoutingSplice p q hadj) =
      parafermionicCoverFinitePairingWalkTurn n hn A p +
        parafermionicCoverFinitePairingStepTurn n A u v +
        parafermionicCoverFinitePairingWalkTurn n hn A q := by
  simp [parafermionicCoverFiniteEdgeCutRoutingSplice,
    parafermionicCoverFinitePairingWalkTurn, Walk.darts_cons,
    List.map_cons, List.sum_cons, add_assoc]

private theorem sourcePhase_of_suffix_turn
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool)
    (hmem : z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (T : ℤ)
    (hturn : parafermionicCoverFinitePairingWalkTurn n hn A
      ((parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil z hmem) = T) :
    parafermionicCoverPathPhaseAtom q n hn A z =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) * (T : ℝ))) := by
  simp [parafermionicCoverPathPhaseAtom, hmem, hturn]

/-- In a two-segment routing, the phase at the second actual source label is
the phase of that actual source segment. -/
theorem parafermionicCoverPathPhaseAtom_routing_two_suffix
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let i := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0
    parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i : ℝ))) := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let p0 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0
  let p1 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  let z := (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1
  let hadj := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0
  let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 p1 hadj
  have hterminal : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i
      (by simpa [i] using h1)
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e i hterminal
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_twoSegments n hn A e h0 h1
  have hfull : parafermionicCoverFiniteOriginExplorationPath n hn A =
      route.copy hs ht := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    simpa [route, p0, p1, hadj, i, r] using hroute
  have hne : (0 : ThreeTerminal) ≠ i := by
    intro heq
    exact h0 (by simpa [i] using heq.symm)
  have hdisj := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
    n hn A e hne
  have hzmem : z ∈ p1.support := by
    exact p1.start_mem_support
  have hnot : z ∉ p0.support := by
    intro hm
    exact hdisj hm hzmem
  have hrouteMem : z ∈ route.support := by
    change z ∈ (parafermionicCoverFiniteEdgeCutRoutingSplice p0 p1 hadj).support
    rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
    exact List.mem_append.mpr (Or.inr hzmem)
  have hmemCopy : z ∈ (route.copy hs ht).support := by
    simpa [Walk.support_copy] using hrouteMem
  have hmem : z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support :=
    hfull.symm ▸ hmemCopy
  have hdrop : (parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil
      z hmem =
      p1.copy rfl ht := by
    have hdropCopy : (route.copy hs ht).dropUntil z hmemCopy = p1.copy rfl ht := by
      rw [Walk.dropUntil_copy]
      simpa [route, parafermionicCoverFiniteEdgeCutRoutingSplice] using
        congrArg (fun w => w.copy rfl ht)
          (dropUntil_append_cons_start p0 p1 hadj hnot)
    exact (dropUntil_eq_of_walk_eq hfull hmem hmemCopy).trans hdropCopy
  have hturn : parafermionicCoverFinitePairingWalkTurn n hn A
      ((parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 hmem) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i := by
    rw [hdrop, pairingWalkTurn_copy_eq]
    exact parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e i
  exact sourcePhase_of_suffix_turn q n hn A _ hmem _ hturn

/-- In a three-segment routing, the phases at the second and third actual
source labels are the phases of the corresponding actual routed suffixes. -/
theorem parafermionicCoverPathPhaseAtom_routing_three_suffixes
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let i := r 0
    let j := r i
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j : ℝ))) ∧
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        ((parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i +
          (if e ∈ A then -1 else 1) +
          parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j : ℤ) : ℝ))) := by
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
  have hreturn := parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return r h0 h1
  have hterminal : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e j = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j
      (by simpa [r, i, j] using hreturn)
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j hterminal
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_threeSegments n hn A e h0 h1
  have hfull : parafermionicCoverFiniteOriginExplorationPath n hn A =
      route.copy hs ht := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    simpa [route, inner, p0, p1, p2, hadj01, hadj12, r, i, j] using hroute
  have hij : i ≠ j := by
    intro heq
    have hfix : r i = i := by simpa [j] using heq.symm
    have hfix0 : r (r 0) = r 0 := by simpa [i] using hfix
    exact h0 (r.injective hfix0)
  have hne0i : (0 : ThreeTerminal) ≠ i := by
    intro heq
    exact h0 (by simpa [i] using heq.symm)
  have hdisj01 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
    n hn A e hne0i
  have hdisj12 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
    n hn A e hij
  let zi := (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1
  let zj := (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1
  have hi_mem1 : zi ∈ p1.support := p1.start_mem_support
  have hj_mem2 : zj ∈ p2.support := p2.start_mem_support
  have hi_not0 : zi ∉ p0.support := fun hm => hdisj01 hm hi_mem1
  have hj_not1 : zj ∉ p1.support := fun hm => hdisj12 hm hj_mem2
  have hinner_mem : zi ∈ inner.support := by
    change zi ∈ (parafermionicCoverFiniteEdgeCutRoutingSplice p1 p2 hadj12).support
    rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
    exact List.mem_append.mpr (Or.inl hi_mem1)
  have hj_inner_mem : zj ∈ inner.support := by
    change zj ∈ (parafermionicCoverFiniteEdgeCutRoutingSplice p1 p2 hadj12).support
    rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
    exact List.mem_append.mpr (Or.inr hj_mem2)
  have hroute_mem_i : zi ∈ route.support := by
    change zi ∈ (parafermionicCoverFiniteEdgeCutRoutingSplice p0 inner hadj01).support
    rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
    exact List.mem_append.mpr (Or.inr hinner_mem)
  have hroute_mem_j : zj ∈ route.support := by
    change zj ∈ (parafermionicCoverFiniteEdgeCutRoutingSplice p0 inner hadj01).support
    rw [parafermionicCoverFiniteEdgeCutRoutingSplice_support]
    exact List.mem_append.mpr (Or.inr hj_inner_mem)
  have hi_copy_mem : zi ∈ (route.copy hs ht).support := by
    simpa [Walk.support_copy] using hroute_mem_i
  have hj_copy_mem : zj ∈ (route.copy hs ht).support := by
    simpa [Walk.support_copy] using hroute_mem_j
  have hi_mem : zi ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support :=
    hfull.symm ▸ hi_copy_mem
  have hj_mem : zj ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support :=
    hfull.symm ▸ hj_copy_mem
  have hdrop_i : (parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil zi hi_mem =
      inner.copy rfl ht := by
    have hdropCopy : (route.copy hs ht).dropUntil zi hi_copy_mem = inner.copy rfl ht := by
      rw [Walk.dropUntil_copy]
      simpa [route, parafermionicCoverFiniteEdgeCutRoutingSplice] using
        congrArg (fun w => w.copy rfl ht)
          (dropUntil_append_cons_start p0 inner hadj01 hi_not0)
    exact (dropUntil_eq_of_walk_eq hfull hi_mem hi_copy_mem).trans hdropCopy
  have hdrop_j : (parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil zj hj_mem =
      p2.copy rfl ht := by
    have hdropInner : inner.dropUntil zj hj_inner_mem = p2 := by
      simpa [inner, parafermionicCoverFiniteEdgeCutRoutingSplice] using
        dropUntil_append_cons_start p1 p2 hadj12 hj_not1
    have hdropCopy : (route.copy hs ht).dropUntil zj hj_copy_mem = p2.copy rfl ht := by
      rw [Walk.dropUntil_copy]
      have hzeroj : (0 : ThreeTerminal) ≠ j := by
        intro heq
        have hfix0 : r 0 = 0 := by
          calc
            r 0 = r j := by rw [heq]
            _ = 0 := by simpa [j, i] using hreturn
        exact h0 hfix0
      have hdisj02 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_support_disjoint_of_ne
        n hn A e hzeroj
      have hj_not0 : zj ∉ p0.support := fun hm => hdisj02 hm hj_mem2
      have houter := dropUntil_append_cons_of_notin_left p0 inner hadj01
        hj_inner_mem hj_not0
      simpa [route, parafermionicCoverFiniteEdgeCutRoutingSplice] using
        congrArg (fun w => w.copy rfl ht) (houter.trans hdropInner)
    exact (dropUntil_eq_of_walk_eq hfull hj_mem hj_copy_mem).trans hdropCopy
  have hturn_j : parafermionicCoverFinitePairingWalkTurn n hn A
      ((parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil zj hj_mem) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j := by
    rw [hdrop_j, pairingWalkTurn_copy_eq]
    exact parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e j
  have hturn_i : parafermionicCoverFinitePairingWalkTurn n hn A
      ((parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil zi hi_mem) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i +
        (if e ∈ A then -1 else 1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j := by
    rw [hdrop_i, pairingWalkTurn_copy_eq]
    have hsplice := pairingWalkTurn_splice n hn A p1 p2 hadj12
    change parafermionicCoverFinitePairingWalkTurn n hn A inner = _
    rw [hsplice,
      parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e i h1,
      ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e i,
      ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e j]
  constructor
  · exact sourcePhase_of_suffix_turn q n hn A zj hj_mem _ hturn_j
  · exact sourcePhase_of_suffix_turn q n hn A zi hi_mem _ hturn_i

end
end PottsContinuity.FKC.FiniteFK
