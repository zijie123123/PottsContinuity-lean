-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutFixedLoopTurning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverSourceTurning
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutToggleTurnDifference
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial

private theorem finiteThree_eq_one_of_ne_zero_ne_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem finiteThree_eq_two_of_ne_zero_ne_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem finiteThree_perm_two_cycle_swap_fixed
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (hi : i ≠ 0) (h0i : π 0 = i) (hi0 : π i = 0) :
    π (threeTerminalSwap i) = threeTerminalSwap i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h20 : π 2 ≠ 0 := by
      intro hh
      have hidx := π.injective (hh.trans hi0.symm)
      norm_num at hidx
    have h21 : π 2 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h22 := finiteThree_eq_two_of_ne_zero_ne_one (π 2) h20 h21
    simpa [threeTerminalSwap] using h22
  · have h10 : π 1 ≠ 0 := by
      intro hh
      have hidx := π.injective (hh.trans hi0.symm)
      norm_num at hidx
    have h12 : π 1 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h11 := finiteThree_eq_one_of_ne_zero_ne_two (π 1) h10 h12
    simpa [threeTerminalSwap] using h11

theorem parafermionicCoverFiniteEdgeCutFixedLoop_turn_eq_four_closed_return_two
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let j := threeTerminalSwap (π 0)
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e j (by
        intro hj
        have heq : threeTerminalSwap (π 0) = threeTerminalSwap 0 := by
          simpa [j, threeTerminalSwap_zero] using hj
        have hi0 := threeTerminalSwap.injective heq
        exact hπ0 (by simpa using hi0)) (by
        have hpfix := finiteThree_perm_two_cycle_swap_fixed π (π 0)
          hπ0 rfl hπ1
        change (if e ∈ A then
          openRoutingSuccessor
            (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e)
          else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) j = j
        simp [hclosed,
          π, j, hpfix])) = 4 := by
  dsimp only
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hj0 : j ≠ 0 := by
    intro hj
    have heq : threeTerminalSwap i = threeTerminalSwap 0 := by
      simpa [j, threeTerminalSwap_zero] using hj
    have hi0 := threeTerminalSwap.injective heq
    exact hπ0 (by simpa [i] using hi0)
  have hpfix := finiteThree_perm_two_cycle_swap_fixed π i hπ0 rfl hπ1
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e j = j := by
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_right hclosed]
    simpa [j] using hpfix
  have hdiff := parafermionicCoverFiniteEdgeCutExplorationTurnDifference_closed_return_two
    n hn A e hclosed hπ0 hπ1
  have hturnA := parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn A
  have hturnT := parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn
    (toggleEdgeConfiguration e A)
  have hdiff' :
      parafermionicCoverFinitePairingWalkTurn n hn
          (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteOriginExplorationPath n hn
            (toggleEdgeConfiguration e A)) -
        parafermionicCoverFinitePairingWalkTurn n hn A
          (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFinitePairingWalkTurn n hn A
          (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e j hj0 hfix) - 4 := by
    simpa [π, i, j] using hdiff
  rw [hturnT, hturnA] at hdiff'
  omega

private theorem finiteThree_perm_three_cycle_swap
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (h0i : π 0 = i) (hi : i ≠ 0) (hi0 : π i ≠ 0) :
    π i = threeTerminalSwap i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h11 : π 1 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h12 := finiteThree_eq_two_of_ne_zero_ne_one (π 1) hi0 h11
    simpa [threeTerminalSwap] using h12
  · have h22 : π 2 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h21 := finiteThree_eq_one_of_ne_zero_ne_two (π 2) hi0 h22
    simpa [threeTerminalSwap] using h21

 theorem finiteThree_toggled_open_fixedpoint_of_three_return
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) =
    parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  have hpcycle : π i = threeTerminalSwap i :=
    finiteThree_perm_three_cycle_swap π i rfl hπ0 hπ1
  have htmem : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  change (if e ∈ toggleEdgeConfiguration e A then
      openRoutingSuccessor
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
          (toggleEdgeConfiguration e A) e)
    else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn
      (toggleEdgeConfiguration e A) e) i = i
  rw [ite_eq_left htmem]
  rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
  change openRoutingSuccessor π i = i
  rw [openRoutingSuccessor_apply, hpcycle]
  have hswap : threeTerminalSwap (threeTerminalSwap i) = i := by
    simp [threeTerminalSwap]
  exact hswap

theorem parafermionicCoverFiniteEdgeCutFixedLoop_turn_eq_neg_four_closed_return_three
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    parafermionicCoverFinitePairingWalkTurn n hn (toggleEdgeConfiguration e A)
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn
        (toggleEdgeConfiguration e A) e i hπ0
        (finiteThree_toggled_open_fixedpoint_of_three_return
          n hn A e hclosed hπ0 hπ1)) = -4 := by
  dsimp only
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  have hpcycle : π i = threeTerminalSwap i :=
    finiteThree_perm_three_cycle_swap π i rfl hπ0 hπ1
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e i = i :=
    finiteThree_toggled_open_fixedpoint_of_three_return n hn A e hclosed hπ0 hπ1
  have hdiff := parafermionicCoverFiniteEdgeCutExplorationTurnDifference_closed_return_three
    n hn A e hclosed hπ0 hπ1
  have hturnA := parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn A
  have hturnT := parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn
    (toggleEdgeConfiguration e A)
  have hdiff' :
      parafermionicCoverFinitePairingWalkTurn n hn
          (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteOriginExplorationPath n hn
            (toggleEdgeConfiguration e A)) -
        parafermionicCoverFinitePairingWalkTurn n hn A
          (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      - parafermionicCoverFinitePairingWalkTurn n hn
          (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutFixedLoop n hn
            (toggleEdgeConfiguration e A) e i hπ0 hfix) - 4 := by
    simpa [π, i] using hdiff
  rw [hturnT, hturnA] at hdiff'
  omega

end PottsContinuity.FKC.FiniteFK
