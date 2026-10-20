-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverToggleSourcePhases.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEdgeCutSuffixPhase
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutFixedSegmentTurns
public import PottsContinuity.FKC.FiniteFK.ParafermionicModifiedPhaseAlgebra
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

private theorem toggleSource_exp_turn_add_two
    (q : ClusterWeight) (x : ℤ) :
    Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((x + 2 : ℤ) : ℝ))) =
      parafermionicModifiedPhase q ^ 2 *
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          (x : ℝ))) := by
  have harg : Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((x + 2 : ℤ) : ℝ)) =
      Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) * (x : ℝ)) +
        Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)) * 2 := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  have htwo : Complex.exp
      (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)) * 2) =
      parafermionicModifiedPhase q ^ 2 := by
    rw [parafermionicModifiedPhase, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [htwo]
  ring

private theorem toggleSource_exp_turn_sub_two
    (q : ClusterWeight) (x : ℤ) :
    Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((x - 2 : ℤ) : ℝ))) =
      (parafermionicModifiedPhase q)⁻¹ ^ 2 *
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          (x : ℝ))) := by
  have harg : Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      ((x - 2 : ℤ) : ℝ)) =
      Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) * (x : ℝ)) -
        Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)) * 2 := by
    push_cast
    ring
  rw [harg, sub_eq_add_neg, Complex.exp_add, Complex.exp_neg]
  have htwo : Complex.exp
      (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2)) * 2) =
      parafermionicModifiedPhase q ^ 2 := by
    rw [parafermionicModifiedPhase, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [htwo]
  have hu := parafermionicModifiedPhase_ne_zero q
  field_simp

private theorem toggleSource_fin3_eq_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem toggleSource_fin3_eq_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem toggleSource_fin3_eq_zero (x : ThreeTerminal)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  have hxlt : x.val < 3 := x.isLt
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem closed_two_swap_facts
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (hπ0 : π 0 = i) (hi : i ≠ 0) (hπi : π i = 0) :
    π (threeTerminalSwap i) = threeTerminalSwap i ∧
      openRoutingSuccessor π 0 = threeTerminalSwap i ∧
      openRoutingSuccessor π (threeTerminalSwap i) = i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h20 : π 2 ≠ 0 := by
      intro h
      have heq := π.injective (h.trans hπi.symm)
      norm_num at heq
    have h21 : π 2 ≠ 1 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h22 : π 2 = 2 := toggleSource_fin3_eq_two (π 2) h20 h21
    simp [threeTerminalSwap, openRoutingSuccessor_apply,
      hπ0, h22]
  · have h10 : π 1 ≠ 0 := by
      intro h
      have heq := π.injective (h.trans hπi.symm)
      norm_num at heq
    have h12 : π 1 ≠ 2 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h11 : π 1 = 1 := toggleSource_fin3_eq_one (π 1) h10 h12
    simp [threeTerminalSwap, openRoutingSuccessor_apply,
      hπ0, h11]

private theorem closed_three_swap_facts
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (hπ0 : π 0 = i) (hi : i ≠ 0) (hπi : π i ≠ 0) :
    π i = threeTerminalSwap i ∧
      π (threeTerminalSwap i) = 0 ∧
      openRoutingSuccessor π 0 = threeTerminalSwap i ∧
      openRoutingSuccessor π (threeTerminalSwap i) = 0 := by
  fin_cases i
  · exact (hi rfl).elim
  · have h11 : π 1 ≠ 1 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h12 : π 1 = 2 := toggleSource_fin3_eq_two (π 1) hπi h11
    have h20 : π 2 = 0 := by
      have h21 : π 2 ≠ 1 := by
        intro h
        have heq := π.injective (h.trans hπ0.symm)
        norm_num at heq
      have h22 : π 2 ≠ 2 := by
        intro h
        have heq := π.injective (h.trans h12.symm)
        norm_num at heq
      exact toggleSource_fin3_eq_zero (π 2) h21 h22
    simp [threeTerminalSwap, openRoutingSuccessor_apply, Equiv.swap_apply_def,
      hπ0, h12, h20]
  · have h22 : π 2 ≠ 2 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h21 : π 2 = 1 := toggleSource_fin3_eq_one (π 2) hπi h22
    have h10 : π 1 = 0 := by
      have h11 : π 1 ≠ 1 := by
        intro h
        have heq := π.injective (h.trans h21.symm)
        norm_num at heq
      have h12 : π 1 ≠ 2 := by
        intro h
        have heq := π.injective (h.trans hπ0.symm)
        norm_num at heq
      exact toggleSource_fin3_eq_zero (π 1) h11 h12
    simp [threeTerminalSwap, openRoutingSuccessor_apply, Equiv.swap_apply_def,
      hπ0, h21, h10]

/-- Actual closed/toggled routing indices in the two-return case. -/
theorem parafermionicCoverFiniteEdgeCutClosedTwoToggleRoutingIndices
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    let j := threeTerminalSwap i
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 = i ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = 0 ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e 0 = j ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e j = i ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e i = 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hi : i ≠ 0 := by simpa [i] using hπ0
  have hπ0' : π 0 = i := rfl
  have hπi : π i = 0 := by simpa [π, i] using hπ1
  have hfacts := closed_two_swap_facts π i hπ0' hi hπi
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hrA : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e = π := by
    simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, hclosed, π]
  have hrT : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e = openRoutingSuccessor π := by
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left htmem]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
  have hzero : openRoutingSuccessor π i = 0 := by
    simp [openRoutingSuccessor_apply, hπi, threeTerminalSwap_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hrA, π]
  · simpa [hrA, i, π] using hπ1
  · rw [hrT]
    simpa [j, i, π] using hfacts.2.1
  · rw [hrT]
    simpa [j, i, π] using hfacts.2.2
  · rw [hrT]
    simpa [i, π] using hzero

/-- Actual closed/toggled routing indices in the three-return case. -/
theorem parafermionicCoverFiniteEdgeCutClosedThreeToggleRoutingIndices
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    let j := π i
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 = i ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = j ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e j = 0 ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e 0 = j ∧
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e j = 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := π i
  have hi : i ≠ 0 := by simpa [i] using hπ0
  have hπ0' : π 0 = i := rfl
  have hπi : π i ≠ 0 := by simpa [π, i] using hπ1
  have hfacts := closed_three_swap_facts π i hπ0' hi hπi
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hrA : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e = π := by
    simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, hclosed, π]
  have hrT : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e = openRoutingSuccessor π := by
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left htmem]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
  have hji : j = threeTerminalSwap i := by simpa [j] using hfacts.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hrA, π]
  · simp [hrA, π]
  · simpa [hrA, i, j, π, hfacts.1] using hfacts.2.1
  · rw [hrT]
    simpa [j, i, π, hfacts.1] using hfacts.2.2.1
  · rw [hrT]
    simpa [j, i, π, hfacts.1] using hfacts.2.2.2

/-- Under a closed edge toggle in the two-return routing, the actual source
atoms differ by the two restored quarter-turns at the intervening segment. -/
theorem parafermionicCoverPathPhaseAtom_toggle_closed_return_two
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    let j := threeTerminalSwap i
    parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 ∧
    parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
      parafermionicModifiedPhase q ^ 2 *
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hi : i ≠ 0 := by simpa [i] using hπ0
  have hπ0' : π 0 = i := rfl
  have hπi : π i = 0 := by simpa [π, i] using hπ1
  have hfacts := closed_two_swap_facts π i hπ0' hi hπi
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hrA : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e = π := by
    simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, hclosed, π]
  have hrT : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e = openRoutingSuccessor π := by
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left htmem]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
  have hopen0 : openRoutingSuccessor π 0 = j := by
    simpa [j] using hfacts.2.1
  have hopenj : openRoutingSuccessor π j = i := hfacts.2.2
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    simpa [hrA] using hπ0
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0 := by
    simpa [hrA, i] using hπ1
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hrT, hopen0]
    intro hz
    apply hi
    exact threeTerminalSwap.injective (by simpa [j, threeTerminalSwap_zero] using hz)
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
          (toggleEdgeConfiguration e A) e 0) ≠ 0 := by
    rw [hrT, hopen0, hopenj]
    exact hi
  have hphaseA := parafermionicCoverPathPhaseAtom_routing_two_suffix
    q n hn A e h0A h1A
  have hphaseT := parafermionicCoverPathPhaseAtom_routing_three_suffixes
    q n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hphaseA' : parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i : ℝ))) := by
    simpa [i, hrA] using hphaseA
  have hphaseT' :
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
            (toggleEdgeConfiguration e A) e i : ℝ))) ∧
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          ((parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
              (toggleEdgeConfiguration e A) e j + (-1) +
            parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
              (toggleEdgeConfiguration e A) e i : ℤ) : ℝ))) := by
    simpa [i, j, hrT, hopen0, hopenj, htmem] using hphaseT
  have hturni := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e i
  have hturnj := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e j
  have hturnjA := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_eq_three_closed_return_two
    n hn A e hclosed hπ0 hπ1
  have hsum : parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
      (toggleEdgeConfiguration e A) e j + (-1) +
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
        (toggleEdgeConfiguration e A) e i =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i + 2 := by
    rw [← hturnj, ← hturni, hturnjA]
    omega
  constructor
  · rw [hphaseT'.1, hphaseA']
    rw [hturni]
  · calc
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
          Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
            ((parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i + 2 : ℤ) : ℝ))) := by
        rw [hphaseT'.2, hsum]
      _ = parafermionicModifiedPhase q ^ 2 *
          Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
            (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i : ℝ))) :=
        toggleSource_exp_turn_add_two q _
      _ = parafermionicModifiedPhase q ^ 2 *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
        rw [← hphaseA']

/-- Under a closed edge toggle in the three-return routing, the actual third
source atom is unchanged and the first is shifted by the inverse squared
modified phase. -/
theorem parafermionicCoverPathPhaseAtom_toggle_closed_return_three
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    let j := π i
    parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
      parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 ∧
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
      (parafermionicModifiedPhase q)⁻¹ ^ 2 *
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := π i
  have hi : i ≠ 0 := by simpa [i] using hπ0
  have hπ0' : π 0 = i := rfl
  have hπi : π i ≠ 0 := by simpa [π, i] using hπ1
  have hfacts := closed_three_swap_facts π i hπ0' hi hπi
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hrA : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e = π := by
    simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, hclosed, π]
  have hrT : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e = openRoutingSuccessor π := by
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left htmem]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
  have hopen0 : openRoutingSuccessor π 0 = j := by
    simpa [j, hfacts.1] using hfacts.2.2.1
  have hopenj : openRoutingSuccessor π j = 0 := by
    simpa [j, hfacts.1] using hfacts.2.2.2
  have hji : j = threeTerminalSwap i := by simpa [j] using hfacts.1
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    simpa [hrA] using hπ0
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0 := by
    simpa [hrA, i] using hπ1
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hrT, hopen0]
    intro hz
    apply hi
    exact threeTerminalSwap.injective (by
      simpa [threeTerminalSwap_zero] using hji.symm.trans hz)
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
          (toggleEdgeConfiguration e A) e 0) = 0 := by
    rw [hrT, hopen0, hopenj]
  have hphaseA := parafermionicCoverPathPhaseAtom_routing_three_suffixes
    q n hn A e h0A h1A
  have hphaseT := parafermionicCoverPathPhaseAtom_routing_two_suffix
    q n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hphaseA' :
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
    simpa [i, j, hrA] using hphaseA
  have hphaseT' : parafermionicCoverPathPhaseAtom q n hn
      (toggleEdgeConfiguration e A)
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e j : ℝ))) := by
    simpa [i, j, hrT, hopen0, hopenj] using hphaseT
  have hturni := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_eq_neg_three_closed_return_three
    n hn A e hclosed hπ0 hπ1
  have hturnj := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e j
  have hsum : parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i +
      (if e ∈ A then -1 else 1) +
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j - 2 := by
    simp [hclosed]
    rw [hturni]
    omega
  constructor
  · rw [hphaseT', hphaseA'.1, hturnj]
  · calc
      parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
          Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
            ((parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j - 2 : ℤ) : ℝ))) := by
        rw [hphaseA'.2, hsum]
      _ = (parafermionicModifiedPhase q)⁻¹ ^ 2 *
          Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
            (parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j : ℝ))) :=
        toggleSource_exp_turn_sub_two q _
      _ = (parafermionicModifiedPhase q)⁻¹ ^ 2 *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 := by
        rw [← hphaseA'.1]

end
end PottsContinuity.FKC.FiniteFK
