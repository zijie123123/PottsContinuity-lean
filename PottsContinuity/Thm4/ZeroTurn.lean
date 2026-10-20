/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverPathPhaseZeroTurn.lean`.
Adaptation: closed [1,4] phases and additive winding counterparts proved from actual suffix recurrence.
No local expected-defect cancellation is assumed.
-/
module

public import PottsContinuity.Thm4.PhaseRecurrence
public import PottsContinuity.Thm4.DirectedPath
public import PottsContinuity.Thm4.PairingPathSupport
public import PottsContinuity.Thm4.WindingRecurrence
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
open LatticePort
noncomputable section

local instance coverZeroTurnAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

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

private theorem finiteCornerCut_vertical_support_iff
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    ((c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) ↔
      ((c, true) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) := by
  constructor
  · intro h
    apply finiteCornerCut_support_adj n hn A h
    simp [parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph]
  · intro h
    apply finiteCornerCut_support_adj n hn A h
    simp [parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph]

private theorem finitePath_vertical_successor_dart
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n)
    (hc : (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = false) :
    ∃ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      d.fst = (c, false) ∧ d.snd = (c, true) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hforward := parafermionicCoverFiniteCornerCut_isPath_forward n hn A
  obtain ⟨i, hvertex, hiBound⟩ := (Walk.mem_support_iff_exists_getVert).mp hc
  have hvertexP : p.getVert i = (c, false) := by simpa [p] using hvertex
  have hiBoundP : i ≤ p.length := by simpa [p] using hiBound
  have hi0 : i ≠ 0 := by
    intro hizero
    subst i
    simp only [Walk.getVert_zero] at hvertexP
    cases hvertexP
  have hiend : i ≠ p.length := by
    intro h
    subst i
    simp only [p.getVert_length] at hvertexP
    cases hvertexP
  have hilt : i < p.length := by omega
  have hidx : i < p.darts.length := by rw [p.length_darts]; exact hilt
  have hsupportIdx : i < p.support.length := by
    simp [SimpleGraph.Walk.length_support]
    omega
  have hsupportNextIdx : i + 1 < p.support.length := by
    simp [SimpleGraph.Walk.length_support]
    omega
  have hdropIdx : i < p.support.dropLast.length := by
    simp [SimpleGraph.Walk.length_support]
    exact hilt
  have hmem : p.darts[i] ∈ p.darts := p.darts.getElem_mem hidx
  have hindex : p.support[i] = (c, false) := by
    rw [← p.getVert_eq_support_getElem (by omega : i ≤ p.length)]
    exact hvertexP
  have hindexNext : p.support[i + 1] = p.getVert (i + 1) := by
    symm
    exact p.getVert_eq_support_getElem (by omega)
  have hfw := hforward (p.darts[i]) (by simp [p])
  simp only [SimpleGraph.Walk.fst_darts_getElem,
    SimpleGraph.Walk.snd_darts_getElem] at hfw
  rw [List.getElem_dropLast hdropIdx, List.getElem_tail] at hfw
  rw [hindex, hindexNext] at hfw
  rcases hnext : (p.getVert (i + 1)).2 with _ | _
  · simp [parafermionicCoverFinitePairingForward, hnext, hflag] at hfw
  · have hfw' : parafermionicCoverIncomingPrimalLeft c = false ∧
        c = (p.getVert (i + 1)).1 := by
      simpa [parafermionicCoverFinitePairingForward, hnext, hflag] using hfw
    have hport : (p.getVert (i + 1)).1 = c := hfw'.2.symm
    refine ⟨p.darts[i], by simp [p], ?_, ?_⟩
    · simp only [SimpleGraph.Walk.fst_darts_getElem]
      rw [List.getElem_dropLast hdropIdx]
      exact hindex
    · simp only [SimpleGraph.Walk.snd_darts_getElem, List.getElem_tail]
      rw [hindexNext]
      apply Prod.ext
      · exact hport
      · exact hnext

private theorem finitePath_vertical_predecessor_dart
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n)
    (hc : (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hflag : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    ∃ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      d.fst = (c, true) ∧ d.snd = (c, false) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hforward := parafermionicCoverFiniteCornerCut_isPath_forward n hn A
  obtain ⟨i, hvertex, hiBound⟩ := (Walk.mem_support_iff_exists_getVert).mp hc
  have hvertexP : p.getVert i = (c, false) := by simpa [p] using hvertex
  have hiBoundP : i ≤ p.length := by simpa [p] using hiBound
  have hi0 : i ≠ 0 := by
    intro hizero
    subst i
    simp only [Walk.getVert_zero] at hvertexP
    cases hvertexP
  have hprevLt : i - 1 < p.length := by omega
  have hprevDartLt : i - 1 < p.darts.length := by rw [p.length_darts]; exact hprevLt
  have hprevSupportLt : i - 1 < p.support.length := by
    simp [SimpleGraph.Walk.length_support]
    omega
  have hprevDropLt : i - 1 < p.support.dropLast.length := by
    simp [SimpleGraph.Walk.length_support]
    exact hprevLt
  have hsupportCurLt : i < p.support.length := by
    simp [SimpleGraph.Walk.length_support]
    omega
  have hindex : p.support[i] = (c, false) := by
    rw [← p.getVert_eq_support_getElem (by omega : i ≤ p.length)]
    exact hvertexP
  have hpredSucc : i - 1 + 1 = i := by omega
  have hmem : p.darts[i - 1] ∈ p.darts := p.darts.getElem_mem hprevDartLt
  have hfw := hforward (p.darts[i - 1]) (by simp [p])
  simp only [SimpleGraph.Walk.fst_darts_getElem,
    SimpleGraph.Walk.snd_darts_getElem] at hfw
  rw [List.getElem_dropLast hprevDropLt, List.getElem_tail] at hfw
  have hfw' : parafermionicCoverFinitePairingForward n hn A
      (p.support[i - 1]) (p.support[i]) := by
    simpa only [hpredSucc] using hfw
  simp only [hindex] at hfw'
  rcases hprev : p.support.dropLast[i - 1] with ⟨x, b⟩
  have hprev' : p.support[i - 1] = (x, b) := by
    simpa only [List.getElem_dropLast hprevDropLt] using hprev
  rw [hprev'] at hfw'
  cases b
  · have hfwFalse : parafermionicCoverIncomingPrimalLeft x = true ∧
        parafermionicCoverFiniteLocalPairPerm n A x = c := by
      simpa [parafermionicCoverFinitePairingForward] using hfw'
    have hlocal := hfwFalse.2
    have hsource := hfwFalse.1
    have hval : (parafermionicCoverFiniteLocalPairPerm n A x).1 =
        parafermionicCoverLocalPair
          (parafermionicCoverConfigurationExtensionState n A) x.1 := rfl
    have hflip := parafermionicCoverIncomingPrimalLeft_localPair
      (parafermionicCoverConfigurationExtensionState n A) x.1
    have htarget : parafermionicCoverIncomingPrimalLeft c.1 = false := by
      have hval' : c.1 = parafermionicCoverLocalPair
          (parafermionicCoverConfigurationExtensionState n A) x.1 := hlocal ▸ hval
      have h := (congrArg parafermionicCoverIncomingPrimalLeft hval').trans hflip
      simpa [hsource] using h
    simp [hflag] at htarget
  · have hfw'' : parafermionicCoverIncomingPrimalLeft x = true ∧ x = c := by
      simpa [parafermionicCoverFinitePairingForward, hflag] using hfw'
    refine ⟨p.darts[i - 1], by simp [p], ?_, ?_⟩
    · simp only [SimpleGraph.Walk.fst_darts_getElem]
      rw [hprev]
      exact congrArg (fun x : ParafermionicCoverFinitePort n => (x, true)) hfw''.2
    · simp only [SimpleGraph.Walk.snd_darts_getElem, List.getElem_tail]
      simp only [hpredSucc, hindex]

theorem parafermionicCoverPathPhaseAtom_false_eq_true
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    parafermionicCoverPathPhaseAtom q n hn A (c, false) =
      parafermionicCoverPathPhaseAtom q n hn A (c, true) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hsupp := finiteCornerCut_vertical_support_iff n hn A c
  by_cases hfalse : (c, false) ∈ p.support
  · have htrue : (c, true) ∈ p.support := by simpa [p] using hsupp.mp hfalse
    by_cases hflag : parafermionicCoverIncomingPrimalLeft c.1 = false
    · obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_vertical_successor_dart n hn A c (by simpa [p] using hfalse) hflag
      have hrec := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A (c, false) (c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hsnd] at hrec
      rw [hturn] at hrec
      simpa using hrec
    · have hflag' : parafermionicCoverIncomingPrimalLeft c.1 = true := by
        cases h : parafermionicCoverIncomingPrimalLeft c.1 <;> simp_all
      obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_vertical_predecessor_dart n hn A c (by simpa [p] using hfalse) hflag'
      have hrec := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A (c, true) (c, false) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hsnd] at hrec
      rw [hturn] at hrec
      have hrec' : parafermionicCoverPathPhaseAtom q n hn A (c, true) =
          parafermionicCoverPathPhaseAtom q n hn A (c, false) := by
        simpa using hrec
      exact hrec'.symm
  · have htrue : (c, true) ∉ p.support := by
      intro h
      exact hfalse ((hsupp).mpr (by simpa [p] using h))
    simp [parafermionicCoverPathPhaseAtom, p, hfalse, htrue]

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

private theorem finitePath_previous_dart_of_internal_vertex
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {z : V} (i : ℕ)
    (hi : 0 < i) (hiEnd : i < p.length) (hvertex : p.getVert i = z) :
    ∃ d ∈ p.darts, d.fst = p.getVert (i - 1) ∧ d.snd = z := by
  have hprev : i - 1 < p.length := by omega
  have hidx : i - 1 < p.darts.length := by rw [p.length_darts]; exact hprev
  have hsupportCur : i < p.support.length := by
    simp [Walk.length_support]
    omega
  have hdropIdx : i - 1 < p.support.dropLast.length := by
    simp [Walk.length_support]
    exact hprev
  have hmem : p.darts[i - 1] ∈ p.darts := p.darts.getElem_mem hidx
  have hindex : p.support[i] = z := by
    rw [← p.getVert_eq_support_getElem (by omega : i ≤ p.length)]
    exact hvertex
  have hpredSucc : i - 1 + 1 = i := by omega
  have hindexPrev : p.support[i - 1] = p.getVert (i - 1) := by
    symm
    exact p.getVert_eq_support_getElem (by omega)
  refine ⟨p.darts[i - 1], hmem, ?_, ?_⟩
  · simp only [Walk.fst_darts_getElem]
    rw [List.getElem_dropLast hdropIdx]
    exact hindexPrev
  · simp only [Walk.snd_darts_getElem, List.getElem_tail]
    simp only [hpredSucc, hindex]

theorem parafermionicCoverPathPhaseAtom_corner_eq_of_not_cut
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n)
    (huncut : c ≠ parafermionicCoverFiniteOriginCornerPort n hn ∧
      c ≠ parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) :
    parafermionicCoverPathPhaseAtom q n hn A (c, true) =
      parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteCornerPairPerm n c, true) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let cut := pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n)
  have hcut : cut c = C c := by
    change pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n) c = C c
    have hnot : ¬ (c = s ∨ c = C s) := by
      intro h
      rcases h with hs | hs
      · exact huncut.1 (by simpa [s] using hs)
      · exact huncut.2 (by simpa [s, C] using hs)
    simp [pairingSingleCutPerm_apply, pairingSingleCut, hnot]
  have hne : c ≠ C c := (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n c).symm
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (c, true) (C c, true) := by
    rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    exact Or.inr (Or.inr ⟨rfl, rfl, hcut, hne⟩)
  have hsupp : (c, true) ∈ p.support ↔ (C c, true) ∈ p.support := by
    constructor
    · intro h
      exact finiteCornerCut_support_adj n hn A (by simpa [p] using h) hadj
    · intro h
      exact finiteCornerCut_support_adj n hn A (by simpa [p] using h) hadj.symm
  by_cases hc : (c, true) ∈ p.support
  · have hCc : (C c, true) ∈ p.support := hsupp.mp hc
    have hstart : (c, true) ≠ (s, true) := by
      intro h
      exact huncut.1 (congrArg Prod.fst h)
    have hend : (c, true) ≠ (C s, true) := by
      intro h
      exact huncut.2 (congrArg Prod.fst h)
    obtain ⟨i, hiPos, hiLt, hvertex⟩ :=
      finitePath_internal_index p (by simpa [p] using hc) hstart hend
    have hforward := parafermionicCoverFiniteCornerCut_isPath_forward n hn A
    by_cases hflag : parafermionicCoverIncomingPrimalLeft c.1 = false
    · obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_next_dart_of_internal_vertex p i hiLt hvertex
      have hfw := hforward d (by simpa [p] using hd)
      rw [hfst, hsnd] at hfw
      have hnext : (p.getVert (i + 1)).2 = true := by
        cases h : (p.getVert (i + 1)).2
        · simp [parafermionicCoverFinitePairingForward, hflag, h] at hfw
        · rfl
      have hfw' : parafermionicCoverIncomingPrimalLeft c.1 = false ∧
          cut c = (p.getVert (i + 1)).1 ∧ c ≠ (p.getVert (i + 1)).1 := by
        simpa [parafermionicCoverFinitePairingForward, hflag, hnext, cut] using hfw
      have hport : (p.getVert (i + 1)).1 = C c := by
        calc
          (p.getVert (i + 1)).1 = cut c := hfw'.2.1.symm
          _ = C c := hcut
      have hstep : d.snd = (C c, true) := by
        rw [hsnd]
        exact Prod.ext hport hnext
      have hrec := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A
          (c, true) (C c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hstep, hturn] at hrec
      simpa using hrec
    · have hflag' : parafermionicCoverIncomingPrimalLeft c.1 = true := by
        cases h : parafermionicCoverIncomingPrimalLeft c.1 <;> simp_all
      obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_previous_dart_of_internal_vertex p i hiPos hiLt hvertex
      have hfw := hforward d (by simpa [p] using hd)
      rw [hfst, hsnd] at hfw
      have hprev : (p.getVert (i - 1)).2 = true := by
        cases h : (p.getVert (i - 1)).2
        · have hfw'' : parafermionicCoverIncomingPrimalLeft
              (p.getVert (i - 1)).1 = false ∧ (p.getVert (i - 1)).1 = c := by
            simpa [parafermionicCoverFinitePairingForward, h] using hfw
          have hcontra : parafermionicCoverIncomingPrimalLeft c.1 = false := by
            rw [← hfw''.2]
            exact hfw''.1
          simp [hflag'] at hcontra
        · rfl
      have hfw' : parafermionicCoverIncomingPrimalLeft (p.getVert (i - 1)).1 = false ∧
          pairingSingleCut C s (p.getVert (i - 1)).1 = c ∧
            (p.getVert (i - 1)).1 ≠ c := by
        simpa [parafermionicCoverFinitePairingForward, hflag', hprev] using hfw
      have hcutInv : Function.Involutive cut :=
        pairingSingleCut_involutive C s
          (parafermionicCoverFiniteCornerPairPerm_involutive n)
      have hport : (p.getVert (i - 1)).1 = C c := by
        have hcutc : cut (p.getVert (i - 1)).1 = c := by
          change pairingSingleCut C s (p.getVert (i - 1)).1 = c
          exact hfw'.2.1
        calc
          (p.getVert (i - 1)).1 = cut (cut (p.getVert (i - 1)).1) :=
            (hcutInv _).symm
          _ = cut c := congrArg cut hcutc
          _ = C c := hcut
      have hsource : d.fst = (C c, true) := by
        have hdsource : d.toProd.1 = (C c, true) := by
          rw [hfst]
          exact Prod.ext hport hprev
        simpa using hdsource
      have hrec := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A
          (C c, true) (c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hsource, hsnd, hturn] at hrec
      have hrec' : parafermionicCoverPathPhaseAtom q n hn A (C c, true) =
          parafermionicCoverPathPhaseAtom q n hn A (c, true) := by
        simpa using hrec
      exact hrec'.symm
  · have hCc : (C c, true) ∉ p.support := by
      intro h
      exact hc (hsupp.mpr (by simpa [p] using h))
    have hCc' : (C c, true) ∉
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
      simpa [p] using hCc
    have hzero : parafermionicCoverPathPhaseAtom q n hn A (c, true) = 0 := by
      simp [parafermionicCoverPathPhaseAtom, p, hc]
    have hzero' : parafermionicCoverPathPhaseAtom q n hn A (C c, true) = 0 := by
      simp [parafermionicCoverPathPhaseAtom, p, hCc]
    rw [hzero, hzero']

theorem parafermionicCoverPathWindingAtom_false_eq_true
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    parafermionicCoverPathWindingAtom n hn A (c, false) =
      parafermionicCoverPathWindingAtom n hn A (c, true) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hsupp := finiteCornerCut_vertical_support_iff n hn A c
  by_cases hfalse : (c, false) ∈ p.support
  · have htrue : (c, true) ∈ p.support := by simpa [p] using hsupp.mp hfalse
    by_cases hflag : parafermionicCoverIncomingPrimalLeft c.1 = false
    · obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_vertical_successor_dart n hn A c (by simpa [p] using hfalse) hflag
      have hrec := parafermionicCoverPathWindingAtom_darts_recurrence n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A (c, false) (c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hsnd] at hrec
      rw [hturn] at hrec
      simpa using hrec
    · have hflag' : parafermionicCoverIncomingPrimalLeft c.1 = true := by
        cases h : parafermionicCoverIncomingPrimalLeft c.1 <;> simp_all
      obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_vertical_predecessor_dart n hn A c (by simpa [p] using hfalse) hflag'
      have hrec := parafermionicCoverPathWindingAtom_darts_recurrence n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A (c, true) (c, false) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hsnd] at hrec
      rw [hturn] at hrec
      have hrec' : parafermionicCoverPathWindingAtom n hn A (c, true) =
          parafermionicCoverPathWindingAtom n hn A (c, false) := by
        simpa using hrec
      exact hrec'.symm
  · have htrue : (c, true) ∉ p.support := by
      intro h
      exact hfalse ((hsupp).mpr (by simpa [p] using h))
    simp [parafermionicCoverPathWindingAtom, p, hfalse, htrue]

theorem parafermionicCoverPathWindingAtom_corner_eq_of_not_cut
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n)
    (huncut : c ≠ parafermionicCoverFiniteOriginCornerPort n hn ∧
      c ≠ parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) :
    parafermionicCoverPathWindingAtom n hn A (c, true) =
      parafermionicCoverPathWindingAtom n hn A
        (parafermionicCoverFiniteCornerPairPerm n c, true) := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let cut := pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n)
  have hcut : cut c = C c := by
    change pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n) c = C c
    have hnot : ¬ (c = s ∨ c = C s) := by
      intro h
      rcases h with hs | hs
      · exact huncut.1 (by simpa [s] using hs)
      · exact huncut.2 (by simpa [s, C] using hs)
    simp [pairingSingleCutPerm_apply, pairingSingleCut, hnot]
  have hne : c ≠ C c := (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n c).symm
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (c, true) (C c, true) := by
    rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    exact Or.inr (Or.inr ⟨rfl, rfl, hcut, hne⟩)
  have hsupp : (c, true) ∈ p.support ↔ (C c, true) ∈ p.support := by
    constructor
    · intro h
      exact finiteCornerCut_support_adj n hn A (by simpa [p] using h) hadj
    · intro h
      exact finiteCornerCut_support_adj n hn A (by simpa [p] using h) hadj.symm
  by_cases hc : (c, true) ∈ p.support
  · have hCc : (C c, true) ∈ p.support := hsupp.mp hc
    have hstart : (c, true) ≠ (s, true) := by
      intro h
      exact huncut.1 (congrArg Prod.fst h)
    have hend : (c, true) ≠ (C s, true) := by
      intro h
      exact huncut.2 (congrArg Prod.fst h)
    obtain ⟨i, hiPos, hiLt, hvertex⟩ :=
      finitePath_internal_index p (by simpa [p] using hc) hstart hend
    have hforward := parafermionicCoverFiniteCornerCut_isPath_forward n hn A
    by_cases hflag : parafermionicCoverIncomingPrimalLeft c.1 = false
    · obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_next_dart_of_internal_vertex p i hiLt hvertex
      have hfw := hforward d (by simpa [p] using hd)
      rw [hfst, hsnd] at hfw
      have hnext : (p.getVert (i + 1)).2 = true := by
        cases h : (p.getVert (i + 1)).2
        · simp [parafermionicCoverFinitePairingForward, hflag, h] at hfw
        · rfl
      have hfw' : parafermionicCoverIncomingPrimalLeft c.1 = false ∧
          cut c = (p.getVert (i + 1)).1 ∧ c ≠ (p.getVert (i + 1)).1 := by
        simpa [parafermionicCoverFinitePairingForward, hflag, hnext, cut] using hfw
      have hport : (p.getVert (i + 1)).1 = C c := by
        calc
          (p.getVert (i + 1)).1 = cut c := hfw'.2.1.symm
          _ = C c := hcut
      have hstep : d.snd = (C c, true) := by
        rw [hsnd]
        exact Prod.ext hport hnext
      have hrec := parafermionicCoverPathWindingAtom_darts_recurrence n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A
          (c, true) (C c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hfst, hstep, hturn] at hrec
      simpa using hrec
    · have hflag' : parafermionicCoverIncomingPrimalLeft c.1 = true := by
        cases h : parafermionicCoverIncomingPrimalLeft c.1 <;> simp_all
      obtain ⟨d, hd, hfst, hsnd⟩ :=
        finitePath_previous_dart_of_internal_vertex p i hiPos hiLt hvertex
      have hfw := hforward d (by simpa [p] using hd)
      rw [hfst, hsnd] at hfw
      have hprev : (p.getVert (i - 1)).2 = true := by
        cases h : (p.getVert (i - 1)).2
        · have hfw'' : parafermionicCoverIncomingPrimalLeft
              (p.getVert (i - 1)).1 = false ∧ (p.getVert (i - 1)).1 = c := by
            simpa [parafermionicCoverFinitePairingForward, h] using hfw
          have hcontra : parafermionicCoverIncomingPrimalLeft c.1 = false := by
            rw [← hfw''.2]
            exact hfw''.1
          simp [hflag'] at hcontra
        · rfl
      have hfw' : parafermionicCoverIncomingPrimalLeft (p.getVert (i - 1)).1 = false ∧
          pairingSingleCut C s (p.getVert (i - 1)).1 = c ∧
            (p.getVert (i - 1)).1 ≠ c := by
        simpa [parafermionicCoverFinitePairingForward, hflag', hprev] using hfw
      have hcutInv : Function.Involutive cut :=
        pairingSingleCut_involutive C s
          (parafermionicCoverFiniteCornerPairPerm_involutive n)
      have hport : (p.getVert (i - 1)).1 = C c := by
        have hcutc : cut (p.getVert (i - 1)).1 = c := by
          change pairingSingleCut C s (p.getVert (i - 1)).1 = c
          exact hfw'.2.1
        calc
          (p.getVert (i - 1)).1 = cut (cut (p.getVert (i - 1)).1) :=
            (hcutInv _).symm
          _ = cut c := congrArg cut hcutc
          _ = C c := hcut
      have hsource : d.fst = (C c, true) := by
        have hdsource : d.toProd.1 = (C c, true) := by
          rw [hfst]
          exact Prod.ext hport hprev
        simpa using hdsource
      have hrec := parafermionicCoverPathWindingAtom_darts_recurrence n hn A d hd
      have hturn : parafermionicCoverFinitePairingStepTurn n A
          (C c, true) (c, true) = 0 := by
        simp [parafermionicCoverFinitePairingStepTurn]
      rw [hsource, hsnd, hturn] at hrec
      have hrec' : parafermionicCoverPathWindingAtom n hn A (C c, true) =
          parafermionicCoverPathWindingAtom n hn A (c, true) := by
        simpa using hrec
      exact hrec'.symm
  · have hCc : (C c, true) ∉ p.support := by
      intro h
      exact hc (hsupp.mpr (by simpa [p] using h))
    have hCc' : (C c, true) ∉
        (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
      simpa [p] using hCc
    have hzero : parafermionicCoverPathWindingAtom n hn A (c, true) = 0 := by
      simp [parafermionicCoverPathWindingAtom, p, hc]
    have hzero' : parafermionicCoverPathWindingAtom n hn A (C c, true) = 0 := by
      simp [parafermionicCoverPathWindingAtom, p, hCc]
    rw [hzero, hzero']

/-- Corner cancellation for the literal source modified path atom, including q=4. -/
lemma parafermionicCoverModifiedPathAtom_corner_eq_of_not_cut
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (huncut : c ≠ parafermionicCoverFiniteOriginCornerPort n hn ∧
      c ≠ parafermionicCoverFiniteCornerPairPerm n (parafermionicCoverFiniteOriginCornerPort n hn)) :
    parafermionicCoverModifiedPathAtom q n hn A (c, true) =
      parafermionicCoverModifiedPathAtom q n hn A
        (parafermionicCoverFiniteCornerPairPerm n c, true) := by
  by_cases hq : q.val = 4
  · simp only [parafermionicCoverModifiedPathAtom, hq, ↓reduceIte]
    exact congrArg Complex.ofReal (parafermionicCoverPathWindingAtom_corner_eq_of_not_cut n hn A c huncut)
  · simp only [parafermionicCoverModifiedPathAtom, hq, ↓reduceIte]
    exact parafermionicCoverPathPhaseAtom_corner_eq_of_not_cut q n hn A c huncut

end

end PottsContinuity.Thm4
