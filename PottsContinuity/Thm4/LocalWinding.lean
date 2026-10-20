module

public import PottsContinuity.Thm4.ZeroTurn
public import PottsContinuity.Thm4.EdgeCutReconnection

/-!
# Additive local winding across a restored queried edge

Unlike an exponential phase, the winding difference across a visited local
pairing is exactly its signed quarter turn. The generic path-index helpers
are copied from Thm4/ZeroTurn.lean. The incoming-turn truth table is ported
from FKconvergence/Medial/ParafermionicCoverEdgeCutReconnectionTurn.lean.
-/

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

private theorem finitePath_internal_index
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {z : V} (hz : z ∈ p.support)
    (hzStart : z ≠ u) (hzEnd : z ≠ v) :
    ∃ i, 0 < i ∧ i < p.length ∧ p.getVert i = z := by
  obtain ⟨i, hvertex, hiBound⟩ := (Walk.mem_support_iff_exists_getVert).mp hz
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    apply hzStart
    simpa using hvertex.symm
  have hiend : i ≠ p.length := by
    intro h
    subst i
    apply hzEnd
    simpa using hvertex.symm
  refine ⟨i, ?_, ?_, hvertex⟩
  · omega
  · omega

private theorem finitePath_next_dart_of_internal_vertex
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {z : V} (i : ℕ)
    (hi : i < p.length) (hvertex : p.getVert i = z) :
    ∃ d ∈ p.darts, d.fst = z ∧ d.snd = p.getVert (i + 1) := by
  have hidx : i < p.darts.length := by rw [p.length_darts]; exact hi
  have hsupportIdx : i < p.support.length := by
    simp [Walk.length_support]
    omega
  have hsupportNextIdx : i + 1 < p.support.length := by
    simp [Walk.length_support]
    omega
  have hdropIdx : i < p.support.dropLast.length := by
    simp [Walk.length_support]
    exact hi
  have hmem : p.darts[i] ∈ p.darts := p.darts.getElem_mem hidx
  have hindex : p.support[i] = z := by
    rw [← p.getVert_eq_support_getElem (by omega : i ≤ p.length)]
    exact hvertex
  have hindexNext : p.support[i + 1] = p.getVert (i + 1) := by
    symm
    exact p.getVert_eq_support_getElem (by omega)
  refine ⟨p.darts[i], hmem, ?_, ?_⟩
  · simp only [Walk.fst_darts_getElem]
    rw [List.getElem_dropLast hdropIdx]
    exact hindex
  · simp only [Walk.snd_darts_getElem, List.getElem_tail]
    exact hindexNext

/-- The next actual dart at an incoming false-layer port follows its local pairing. -/
theorem exploration_localPair_successor_dart (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hvisit : (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    ∃ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      d.fst = (c, false) ∧ d.snd = (parafermionicCoverFiniteLocalPairPerm n A c, false) := by
  classical
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  obtain ⟨i, _, hi, hvertex⟩ := finitePath_internal_index p hvisit
    (by intro h; exact Bool.noConfusion (congrArg Prod.snd h))
    (by intro h; exact Bool.noConfusion (congrArg Prod.snd h))
  obtain ⟨d, hd, hfst, _⟩ := finitePath_next_dart_of_internal_vertex p i hi hvertex
  have hfw := parafermionicCoverFiniteCornerCut_isPath_forward n hn A d hd
  rw [hfst] at hfw
  cases hb : d.snd.2 with
  | false =>
    have hp : parafermionicCoverFiniteLocalPairPerm n A c = d.snd.1 := by
      simpa [parafermionicCoverFinitePairingForward, hb, hflag] using hfw
    exact ⟨d, hd, hfst, Prod.ext hp.symm hb⟩
  | true =>
    have hbad : parafermionicCoverIncomingPrimalLeft c.1 = false := by
      exact (show parafermionicCoverIncomingPrimalLeft c.1 = false ∧ c = d.snd.1 by
        simpa [parafermionicCoverFinitePairingForward, hb] using hfw).1
    rw [hflag] at hbad
    cases hbad

/-- Across a visited incoming local pairing, actual suffix windings differ by
pi/2 times the actual local turn exponent. -/
theorem pathWinding_localPair_difference_of_visit (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hvisit : (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverPathWindingAtom n hn A (c, true) -
        parafermionicCoverPathWindingAtom n hn A
          (parafermionicCoverFiniteLocalPairPerm n A c, true) =
      (Real.pi / 2) * (parafermionicCoverMedialTurnExponent
        (parafermionicCoverConfigurationExtensionState n A) c.1 : ℝ) := by
  obtain ⟨d, hd, hfst, hsnd⟩ := exploration_localPair_successor_dart n hn A c hvisit hflag
  have hrec := parafermionicCoverPathWindingAtom_darts_recurrence n hn A d hd
  rw [hfst, hsnd] at hrec
  simp [parafermionicCoverFinitePairingStepTurn] at hrec
  rw [parafermionicCoverPathWindingAtom_false_eq_true,
    parafermionicCoverPathWindingAtom_false_eq_true] at hrec
  linarith

private theorem finiteCornerCut_support_adj
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hu : u ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    v ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  let L := parafermionicCoverFiniteLocalPairPerm n A
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let B := pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n)
  have hL := parafermionicCoverFiniteLocalPairPerm_involutive n A
  have hC := parafermionicCoverFiniteCornerPairPerm_involutive n
  have hB := pairingSingleCut_involutive C s hC
  have hfree := parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A
  have hst : s ≠ C s := parafermionicCoverFiniteCornerPairPerm_origin_ne n hn
  have hBfixed : ∀ x, B x = x ↔ x = s ∨ x = C s := by
    intro x
    exact pairingSingleCutPerm_fixed_iff C s x hC
      (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n)
  have hgraph : parafermionicCoverFiniteCornerCutPairingGraph n hn A =
      pairingGraph L B hL hB := rfl
  rw [hgraph] at hadj
  exact pairingGraph_path_support_closed_under_adj L B hL hB hfree hst hBfixed
    (parafermionicCoverFiniteOriginExplorationPath n hn A)
    (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A) hu hadj

/-- Absence of an actual local-pair visit forces zero winding at both paired ports. -/
theorem pathWinding_localPair_zero_of_no_visit (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hno : (c, false) ∉ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :
    parafermionicCoverPathWindingAtom n hn A (c, true) = 0 ∧
      parafermionicCoverPathWindingAtom n hn A
        (parafermionicCoverFiniteLocalPairPerm n A c, true) = 0 := by
  have hpairno : (parafermionicCoverFiniteLocalPairPerm n A c, false) ∉
      (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
    intro hvisit
    apply hno
    apply finiteCornerCut_support_adj n hn A hvisit
    apply SimpleGraph.Adj.symm
    rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl,
      fun h => parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A c h.symm⟩)
  constructor
  · rw [← parafermionicCoverPathWindingAtom_false_eq_true n hn A c]
    simp [parafermionicCoverPathWindingAtom, hno]
  · rw [← parafermionicCoverPathWindingAtom_false_eq_true n hn A
      (parafermionicCoverFiniteLocalPairPerm n A c)]
    simp [parafermionicCoverPathWindingAtom, hpairno]

/-- The incoming-pair winding difference is a single actual signed quarter turn
on the visit event, and zero off that event. -/
theorem pathWinding_localPair_difference (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverPathWindingAtom n hn A (c, true) -
        parafermionicCoverPathWindingAtom n hn A
          (parafermionicCoverFiniteLocalPairPerm n A c, true) =
      if (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support then
        (Real.pi / 2) * (parafermionicCoverMedialTurnExponent
          (parafermionicCoverConfigurationExtensionState n A) c.1 : ℝ)
      else 0 := by
  classical
  split_ifs with hvisit
  · exact pathWinding_localPair_difference_of_visit n hn A c hvisit hflag
  · obtain ⟨h₁, h₂⟩ := pathWinding_localPair_zero_of_no_visit n hn A c hvisit
    rw [h₁, h₂, sub_self]

private theorem medialTurnPositive_eq_incoming_xor_state
    (ω : LatticeBond → Bool) (p : LatticePort) :
    medialTurnPositive ω p = (medialIncomingPrimalLeft p != ω p.bond) := by
  rcases p with ⟨⟨⟨x, y⟩, axis⟩, tip, side⟩
  cases axis with
  | horizontal =>
      cases tip <;> cases side <;>
        cases hstate : ω ⟨(x, y), LatticeAxis.horizontal⟩ <;>
        simp [medialTurnPositive, medialIncomingPrimalLeft, hstate]
  | vertical =>
      cases tip <;> cases side <;>
        cases hstate : ω ⟨(x, y), LatticeAxis.vertical⟩ <;>
        simp [medialTurnPositive, medialIncomingPrimalLeft, hstate]

private theorem parafermionicCoverFiniteEdgeCutSinkTurnExponent
    (n : ℕ) (_hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e)
    (hin : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverMedialTurnExponent
        (parafermionicCoverConfigurationExtensionState n A) c.1 =
      if e ∈ A then -1 else 1 := by
  have hstate := parafermionicCoverFiniteEdgeCutPort_state_eq_mem n A e c hc
  unfold parafermionicCoverMedialTurnExponent parafermionicCoverMedialTurnPositive
  rw [medialTurnPositive_eq_incoming_xor_state,
    parafermionicCoverPortLocalBaseState_at, hstate]
  change (if medialIncomingPrimalLeft c.1.1 != decide (e ∈ A) then (1 : ℤ) else -1) =
    if e ∈ A then -1 else 1
  change medialIncomingPrimalLeft c.1.1 = true at hin
  by_cases he : e ∈ A <;> simp [he, hin]

/-- On an actual queried incoming port, the winding difference is one positive
quarter turn for a closed edge and one negative quarter turn for an open edge. -/
theorem pathWinding_queried_difference (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverPathWindingAtom n hn A (c, true) -
        parafermionicCoverPathWindingAtom n hn A
          (parafermionicCoverFiniteLocalPairPerm n A c, true) =
      if (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support then
        (Real.pi / 2) * (if e ∈ A then (-1 : ℝ) else 1)
      else 0 := by
  classical
  rw [pathWinding_localPair_difference n hn A c hflag,
    parafermionicCoverFiniteEdgeCutSinkTurnExponent n hn A e c hc hflag]
  split_ifs <;> simp

end
end PottsContinuity.Thm4
