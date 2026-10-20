module

public import PottsContinuity.Thm4.WindingRoutingCounts
public import PottsContinuity.Thm4.ThreeReturnConnection

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

private theorem openRouting_of_two_return (π : Equiv.Perm (Fin 3))
    (h0 : π 0 ≠ 0) (h1 : π (π 0) = 0) :
    openRoutingSuccessor π 0 ≠ 0 ∧
      openRoutingSuccessor π (openRoutingSuccessor π 0) ≠ 0 := by
  revert h0 h1
  fin_cases π <;> decide

private theorem openRouting_of_three_return (π : Equiv.Perm (Fin 3))
    (h0 : π 0 ≠ 0) (h1 : π (π 0) ≠ 0) :
    openRoutingSuccessor π 0 ≠ 0 ∧
      openRoutingSuccessor π (openRoutingSuccessor π 0) = 0 := by
  revert h0 h1
  fin_cases π <;> decide

private theorem closed_routing_successors (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A) :
    parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e =
        parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e ∧
      parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn (toggleEdgeConfiguration e A) e =
        openRoutingSuccessor (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) := by
  have ht : e ∈ toggleEdgeConfiguration e A := (toggleEdgeConfiguration_mem e A).2 he
  constructor
  · simp only [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_right he]
  · simp only [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_left ht,
      ← parafermionicCoverFiniteEdgeCutTerminalPermutation_toggle_eq n hn A e]

/-- In the actual closed two-return class the winding defects before and after
opening are pi/2 and -pi. No mass or planar nonconnection assertion is assumed. -/
theorem windingAtomicDefect_closed_two_return_values (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    windingAtomicDefect n hn e A = Real.pi / 2 ∧
      windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = -Real.pi := by
  have hr := closed_routing_successors n hn A e he
  have hopen := openRouting_of_two_return
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) h0 h1
  have hcountA := windingIncomingVisitCount_two_segments n hn A e
    (by simpa only [hr.1] using h0) (by simpa only [hr.1] using h1)
  have hcountT := windingIncomingVisitCount_three_segments n hn (toggleEdgeConfiguration e A) e
    (by simpa only [hr.2] using hopen.1) (by simpa only [hr.2] using hopen.2)
  have ht : e ∈ toggleEdgeConfiguration e A := (toggleEdgeConfiguration_mem e A).2 he
  constructor
  · rw [windingAtomicDefect_eq_signed_visit_count, hcountA]
    simp only [ite_eq_right he, Nat.cast_one, mul_one]
  · rw [windingAtomicDefect_eq_signed_visit_count, hcountT]
    simp only [ite_eq_left ht, Nat.cast_ofNat]
    ring

/-- In the actual closed three-return class the winding defects before and after
opening are pi and -pi/2. This uses actual routing and local additive winding. -/
theorem windingAtomicDefect_closed_three_return_values (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    windingAtomicDefect n hn e A = Real.pi ∧
      windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = -(Real.pi / 2) := by
  have hr := closed_routing_successors n hn A e he
  have hopen := openRouting_of_three_return
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e) h0 h1
  have hcountA := windingIncomingVisitCount_three_segments n hn A e
    (by simpa only [hr.1] using h0) (by simpa only [hr.1] using h1)
  have hcountT := windingIncomingVisitCount_two_segments n hn (toggleEdgeConfiguration e A) e
    (by simpa only [hr.2] using hopen.1) (by simpa only [hr.2] using hopen.2)
  have ht : e ∈ toggleEdgeConfiguration e A := (toggleEdgeConfiguration_mem e A).2 he
  constructor
  · rw [windingAtomicDefect_eq_signed_visit_count, hcountA]
    simp only [ite_eq_right he, Nat.cast_ofNat, mul_one]
    ring
  · rw [windingAtomicDefect_eq_signed_visit_count, hcountT]
    simp only [ite_eq_left ht, Nat.cast_one, mul_one, mul_neg, mul_one]

/-- The actual closed three-return q=4 winding probability pair cancels under
any boundary partition, at the explicit self-dual edge probability 2/3. -/
theorem windingAtomicDefect_three_return_probability_pair_four
    (n : ℕ) (hn : 1 ≤ n) (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩) ξ A * windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩) ξ (toggleEdgeConfiguration e A) *
        windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  obtain ⟨hA, hT⟩ := windingAtomicDefect_closed_three_return_values n hn A e he h0 h1
  have hprob := threeReturn_selfDual_probability n hn ⟨4, by norm_num⟩ ξ A e he h0 h1
  have hweight : loopWeight (4 : ℝ) = 2 := by norm_num [loopWeight]
  rw [hweight] at hprob
  rw [hA, hT, hprob]
  ring

end
end PottsContinuity.Thm4
