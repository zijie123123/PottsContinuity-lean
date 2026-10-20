-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutFixedSegmentTurns.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutFixedLoopTurning
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutFixedLoop
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutSegmentTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

private theorem fixedSegment_three_eq_one_of_ne_zero_ne_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fixedSegment_three_eq_two_of_ne_zero_ne_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem fixedSegment_two_return_swap_fixed
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
    have h22 := fixedSegment_three_eq_two_of_ne_zero_ne_one (π 2) h20 h21
    simpa [threeTerminalSwap] using h22
  · have h10 : π 1 ≠ 0 := by
      intro hh
      have hidx := π.injective (hh.trans hi0.symm)
      norm_num at hidx
    have h12 : π 1 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h11 := fixedSegment_three_eq_one_of_ne_zero_ne_two (π 1) h10 h12
    simpa [threeTerminalSwap] using h11

private theorem fixedSegment_three_return_swap_image
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (h0i : π 0 = i) (hi : i ≠ 0) (hi0 : π i ≠ 0) :
    π i = threeTerminalSwap i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h11 : π 1 ≠ 1 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h12 := fixedSegment_three_eq_two_of_ne_zero_ne_one (π 1) hi0 h11
    simpa [threeTerminalSwap] using h12
  · have h22 : π 2 ≠ 2 := by
      intro hh
      have hidx := π.injective (hh.trans h0i.symm)
      norm_num at hidx
    have h21 := fixedSegment_three_eq_one_of_ne_zero_ne_two (π 2) hi0 h22
    simpa [threeTerminalSwap] using h21

/-- In the closed two-return case, the actual original source segment has turn 3. -/
theorem parafermionicCoverFiniteEdgeCutSourceSegmentTurn_eq_three_closed_return_two
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e
      (threeTerminalSwap
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)) = 3 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hj0 : j ≠ 0 := by
    intro hj
    have heq : threeTerminalSwap i = threeTerminalSwap 0 := by
      simpa [j, threeTerminalSwap_zero] using hj
    exact hπ0 (by simpa [i] using threeTerminalSwap.injective heq)
  have hpfix : π j = j :=
    fixedSegment_two_return_swap_fixed π i hπ0 rfl hπ1
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e j = j := by
    simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, hclosed, π, j, hpfix]
  have hloop := parafermionicCoverFiniteEdgeCutFixedLoop_turn_eq_four_closed_return_two
    n hn A e hclosed hπ0 hπ1
  have hloop' : parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e j hj0 hfix) = 4 := by
    simpa [π, i, j] using hloop
  have hturn := parafermionicCoverFiniteEdgeCutFixedLoop_turn n hn A e j hj0 hfix
  rw [hloop'] at hturn
  have hturn' : 4 = parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e
      (threeTerminalSwap (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)) + 1 := by
    simpa [π, i, j, hclosed] using hturn
  omega

/-- In the closed three-return case, the actual original source segment has turn -3. -/
theorem parafermionicCoverFiniteEdgeCutSourceSegmentTurn_eq_neg_three_closed_return_three
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = -3 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  have hpcycle : π i = threeTerminalSwap i :=
    fixedSegment_three_return_swap_image π i rfl hπ0 hπ1
  have hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e i = i := by
    have ht : e ∈ toggleEdgeConfiguration e A := by
      simp [toggleEdgeConfiguration, hclosed]
    rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left ht]
    rw [← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]
    change threeTerminalSwap (π i) = i
    rw [hpcycle]
    simp [threeTerminalSwap]
  have hloop := parafermionicCoverFiniteEdgeCutFixedLoop_turn_eq_neg_four_closed_return_three
    n hn A e hclosed hπ0 hπ1
  have hloop' : parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A)
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn
        (toggleEdgeConfiguration e A) e i hπ0 hfix) = -4 := by
    simpa [π, i] using hloop
  have hturn := parafermionicCoverFiniteEdgeCutFixedLoop_turn n hn
    (toggleEdgeConfiguration e A) e i hπ0 hfix
  have ht : e ∈ toggleEdgeConfiguration e A := by
    simp [toggleEdgeConfiguration, hclosed]
  rw [hloop'] at hturn
  simp [ht] at hturn
  have htoggle := parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq n hn A e i
  have hsegT : parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
      (toggleEdgeConfiguration e A) e i = -3 := by omega
  rw [htoggle]
  exact hsegT

end
end PottsContinuity.FKC.FiniteFK
