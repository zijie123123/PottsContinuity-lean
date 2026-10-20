module

public import PottsContinuity.Thm4.TwoReturnNonconnection
public import PottsContinuity.Thm4.WindingToggle
public import PottsContinuity.Thm4.ZeroReturnPermutation

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

local instance windingCancellationConfigFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _

/-- The actual closed two-return winding pair cancels under the free q=4 law
at the explicit self-dual parameter. Nonconnection is proved by planar separation. -/
theorem windingAtomicDefect_two_return_probability_pair_four
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
        windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) * windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  obtain ⟨hA, hT⟩ := windingAtomicDefect_closed_two_return_values n hn A e he h0 h1
  have hprob := twoReturn_selfDual_free_probability n hn ⟨4, by norm_num⟩ A e he h0 h1
  have hweight : loopWeight (4 : ℝ) = 2 := by norm_num [loopWeight]
  rw [hweight] at hprob
  rw [hA, hT, ← hprob]
  ring

/-- All actual return classes give cancellation for a closed queried edge. -/
theorem windingAtomicDefect_closed_probability_pair_four
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A) :
    configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
        windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) * windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  by_cases h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0
  · exact windingAtomicDefect_permutation_zero_probability_pair n hn ⟨4, by norm_num⟩
      (BoundaryCondition.free ∅) A e h0
  · by_cases h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0
    · exact windingAtomicDefect_two_return_probability_pair_four n hn A e he h0 h1
    · exact windingAtomicDefect_three_return_probability_pair_four n hn
        (BoundaryCondition.free ∅) A e he h0 h1

/-- The actual q=4 free-law winding defect cancels in each unordered edge-toggle
pair, for every configuration and every queried finite cover edge. -/
theorem windingAtomicDefect_probability_pair_cancel_four
    (n : ℕ) (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
        windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) * windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  by_cases he : e ∉ A
  · exact windingAtomicDefect_closed_probability_pair_four n hn A e he
  · have ht : e ∉ toggleEdgeConfiguration e A := by
      rw [toggleEdgeConfiguration_mem]
      exact not_not.mpr (not_not.mp he)
    have h := windingAtomicDefect_closed_probability_pair_four n hn (toggleEdgeConfiguration e A) e ht
    rw [toggleEdgeConfiguration_involutive] at h
    simpa only [add_comm] using h

/-- The complete real finite FK expectation of each actual local winding defect
is zero at q=4 and explicit p=2/3. -/
theorem windingAtomicDefect_configuration_sum_four (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (∑ A : Configuration (ParafermionicAmbientGraph n),
      configurationProbability (ParafermionicAmbientGraph n)
        (selfDualParameters ⟨4, by norm_num⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
        windingAtomicDefect n hn e A) = 0 := by
  let F : Configuration (ParafermionicAmbientGraph n) → ℝ := fun A =>
    configurationProbability (ParafermionicAmbientGraph n)
      (selfDualParameters ⟨4, by norm_num⟩)
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
      windingAtomicDefect n hn e A
  have hpairs : (∑ A, (F A + F (toggleEdgeConfiguration e A))) = 0 :=
    Finset.sum_eq_zero (fun A _ => windingAtomicDefect_probability_pair_cancel_four n hn e A)
  have hsum : (∑ A, F (toggleEdgeConfiguration e A)) = ∑ A, F A :=
    Equiv.sum_comp (toggleEdgeConfigurationEquiv e) F
  rw [Finset.sum_add_distrib, hsum] at hpairs
  change (∑ A, F A) = 0
  linarith

end
end PottsContinuity.Thm4
