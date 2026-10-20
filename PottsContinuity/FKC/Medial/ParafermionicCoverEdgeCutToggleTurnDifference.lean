-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutToggleTurnDifference.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutFixedLoop
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

private theorem closed_toggle_routing_successors
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hclosed : e ∉ A) :
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e =
        parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e ∧
      parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e =
        openRoutingSuccessor (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) := by
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  constructor
  · change (if e ∈ A then openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e)
    else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) = _
    simp [hclosed]
  · change (if e ∈ toggleEdgeConfiguration e A then openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
        (toggleEdgeConfiguration e A) e)
    else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
      (toggleEdgeConfiguration e A) e) = _
    rw [ite_eq_left htmem]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]

private theorem fin3_eq_zero_of_ne_one_ne_two (x : ThreeTerminal)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  have hxlt : x.val < 3 := x.isLt
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fin3_eq_one_of_ne_zero_ne_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fin3_eq_two_of_ne_zero_ne_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem closed_two_cycle_open_routing_facts
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (h0i : π 0 = i) (hi : i ≠ 0) (h1 : π i = 0) :
    openRoutingSuccessor π 0 = threeTerminalSwap i ∧
      openRoutingSuccessor π (threeTerminalSwap i) = i ∧
      openRoutingSuccessor π i = 0 ∧
      π (threeTerminalSwap i) = threeTerminalSwap i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h20 : π 2 ≠ 0 := by
      intro hh
      have hidx := π.injective (hh.trans h1.symm)
      exact (by norm_num at hidx)
    have h21 : π 2 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h22 := fin3_eq_two_of_ne_zero_ne_one (π 2) h20 h21
    have hp1 : π 1 = 0 := by simpa using h1
    simp [openRoutingSuccessor_apply, threeTerminalSwap_one,
      threeTerminalSwap_two, threeTerminalSwap_zero, h0i, hp1, h22]
  · have h10 : π 1 ≠ 0 := by
      intro hh
      have hidx := π.injective (hh.trans h1.symm)
      exact (by norm_num at hidx)
    have h12 : π 1 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h11 := fin3_eq_one_of_ne_zero_ne_two (π 1) h10 h12
    have hp2 : π 2 = 0 := by simpa using h1
    simp [openRoutingSuccessor_apply, threeTerminalSwap_one,
      threeTerminalSwap_two, threeTerminalSwap_zero, h0i, hp2, h11]

private theorem closed_three_cycle_open_routing_facts
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (h0i : π 0 = i) (hi : i ≠ 0) (h1 : π i ≠ 0) :
    π i = threeTerminalSwap i ∧
      π (π i) = 0 ∧
      openRoutingSuccessor π 0 = π i ∧
      openRoutingSuccessor π (π i) = 0 ∧
      openRoutingSuccessor π i = i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h11 : π 1 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h12 := fin3_eq_two_of_ne_zero_ne_one (π 1) h1 h11
    have h21 : π 2 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h22 : π 2 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h12.symm)
      exact (by norm_num at hidx)
    have h20 := fin3_eq_zero_of_ne_one_ne_two (π 2) h21 h22
    have hp1 : π 1 = 2 := by simpa using h12
    have hp2 : π 2 = 0 := by simpa using h20
    simp [openRoutingSuccessor_apply, threeTerminalSwap_one,
      threeTerminalSwap_two, threeTerminalSwap_zero, h0i, hp1, hp2]
  · have h22 : π 2 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h21 := fin3_eq_one_of_ne_zero_ne_two (π 2) h1 h22
    have h11 : π 1 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h21.symm)
      exact (by norm_num at hidx)
    have h10 : π 1 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      exact (by norm_num at hidx)
    have h10' := fin3_eq_zero_of_ne_one_ne_two (π 1) h11 h10
    have hp2 : π 2 = 1 := by simpa using h21
    have hp1 : π 1 = 0 := by simpa using h10'
    simp [openRoutingSuccessor_apply, threeTerminalSwap_one,
      threeTerminalSwap_two, threeTerminalSwap_zero, h0i, hp2, hp1]

theorem parafermionicCoverFiniteEdgeCutExplorationTurnDifference_closed_return_two
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let j := threeTerminalSwap (π 0)
    parafermionicCoverFinitePairingWalkTurn n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteOriginExplorationPath n hn (toggleEdgeConfiguration e A)) -
      parafermionicCoverFinitePairingWalkTurn n hn A
        (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFinitePairingWalkTurn n hn A
        (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e j (by
          intro hj
          have hEq : threeTerminalSwap (π 0) = threeTerminalSwap 0 := by
            simpa [j, threeTerminalSwap_zero] using hj
          have hi0 := threeTerminalSwap.injective hEq
          exact hπ0 (by simpa using hi0)) (by
          have hfacts := closed_two_cycle_open_routing_facts π (π 0) rfl hπ0 hπ1
          rw [(closed_toggle_routing_successors n hn A e hclosed).1]
          exact hfacts.2.2.2)) - 4 := by
  dsimp only
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hroutes := closed_toggle_routing_successors n hn A e hclosed
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    simpa only [hroutes.1] using hπ0
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0 := by
    simpa only [hroutes.1] using hπ1
  have hfacts := closed_two_cycle_open_routing_facts π i rfl hπ0 hπ1
  have hopen0 : openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) 0 =
      threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) := by
    simpa [π, i] using hfacts.1
  have hopenj : openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e)
      (threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)) =
      parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 := by
    simpa [π, i] using hfacts.2.1
  have hj0 : j ≠ 0 := by
    intro hj
    have heq : threeTerminalSwap i = threeTerminalSwap 0 := by
      simpa [j, threeTerminalSwap_zero] using hj
    have hi0 := threeTerminalSwap.injective heq
    exact hπ0 (by simpa [i] using hi0)
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hroutes.2]
    change openRoutingSuccessor π 0 ≠ 0
    rw [hfacts.1]
    exact hj0
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e 0) ≠ 0 := by
    rw [hroutes.2]
    change openRoutingSuccessor π (openRoutingSuccessor π 0) ≠ 0
    rw [hfacts.1, hfacts.2.1]
    exact hπ0
  have hturnA := parafermionicCoverFiniteEdgeCutRoutingWalk_turn_twoSegments
    n hn A e h0A h1A
  have hturnT := parafermionicCoverFiniteEdgeCutRoutingWalk_turn_threeSegments
    n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hturnA' : parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e 0 + 1 +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e (π 0) := by
    simpa [hroutes.1, hclosed] using hturnA
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hturnT' : parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A)
      (parafermionicCoverFiniteOriginExplorationPath n hn (toggleEdgeConfiguration e A)) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e 0 + (-1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e (threeTerminalSwap (π 0)) + (-1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e (π 0) := by
    simpa [hroutes.2, hopen0, hopenj, htmem] using hturnT
  rw [hturnT', hturnA']
  rw [← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e 0,
    ← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e
      (threeTerminalSwap (π 0)),
    ← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e (π 0)]
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (threeTerminalSwap (π 0)) = threeTerminalSwap (π 0) := by
    rw [hroutes.1]
    exact hfacts.2.2.2
  rw [parafermionicCoverFiniteEdgeCutFixedLoop_turn n hn A e
    (threeTerminalSwap (π 0)) hj0 hfix]
  simp [hclosed]
  ring_nf

theorem parafermionicCoverFiniteEdgeCutExplorationTurnDifference_closed_return_three
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    parafermionicCoverFinitePairingWalkTurn n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteOriginExplorationPath n hn (toggleEdgeConfiguration e A)) -
      parafermionicCoverFinitePairingWalkTurn n hn A
        (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      - parafermionicCoverFinitePairingWalkTurn n hn (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeCutFixedLoop n hn (toggleEdgeConfiguration e A) e i hπ0 (by
          rw [(closed_toggle_routing_successors n hn A e hclosed).2]
          have hfacts := closed_three_cycle_open_routing_facts π (π 0) rfl hπ0 hπ1
          exact hfacts.2.2.2.2)) - 4 := by
  dsimp only
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  have hroutes := closed_toggle_routing_successors n hn A e hclosed
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    simpa only [hroutes.1] using hπ0
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0 := by
    simpa only [hroutes.1] using hπ1
  have hfacts := closed_three_cycle_open_routing_facts π i rfl hπ0 hπ1
  have hopen0π : openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) 0 =
      parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) := by
    simpa [π, i] using hfacts.2.2.1
  have hcycle : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) =
      threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) := by
    simpa [π, i] using hfacts.1
  have hreturn : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)) = 0 := by
    simpa [π, i] using hfacts.2.1
  have hopen0 : openRoutingSuccessor
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) 0 =
      threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) := by
    rw [hopen0π, hcycle]
  have hj0 : threeTerminalSwap i ≠ 0 := by
    intro hj
    have heq : threeTerminalSwap i = threeTerminalSwap 0 := by
      simpa [threeTerminalSwap_zero] using hj
    have hi0 := threeTerminalSwap.injective heq
    exact hπ0 (by simpa [i] using hi0)
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hroutes.2]
    change openRoutingSuccessor π 0 ≠ 0
    rw [hfacts.2.2.1]
    exact hπ1
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
        (toggleEdgeConfiguration e A) e 0) = 0 := by
    rw [hroutes.2]
    change openRoutingSuccessor π (openRoutingSuccessor π 0) = 0
    rw [hfacts.2.2.1, hfacts.2.2.2.1]
  have hturnA := parafermionicCoverFiniteEdgeCutRoutingWalk_turn_threeSegments
    n hn A e h0A h1A
  have hturnT := parafermionicCoverFiniteEdgeCutRoutingWalk_turn_twoSegments
    n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hturnA' : parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e 0 + 1 +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e (π 0) + 1 +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e
          (threeTerminalSwap (π 0)) := by
    simpa [hroutes.1, hclosed, hcycle, hreturn] using hturnA
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  have hturnT' : parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A)
      (parafermionicCoverFiniteOriginExplorationPath n hn (toggleEdgeConfiguration e A)) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e 0 + (-1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
          (toggleEdgeConfiguration e A) e (threeTerminalSwap (π 0)) := by
    simpa [hroutes.2, hopen0, htmem] using hturnT
  rw [hturnT', hturnA']
  rw [← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e 0,
    ← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e
      (threeTerminalSwap (π 0))]
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e (π 0) = π 0 := by
    rw [hroutes.2]
    exact hfacts.2.2.2.2
  rw [parafermionicCoverFiniteEdgeCutFixedLoop_turn n hn
    (toggleEdgeConfiguration e A) e (π 0) hπ0 hfix]
  rw [← parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e (π 0)]
  simp [htmem]
  ring_nf

end
end PottsContinuity.FKC.FiniteFK
