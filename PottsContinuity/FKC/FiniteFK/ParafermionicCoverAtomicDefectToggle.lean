-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverAtomicDefectToggle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverAtomicDefectRouting
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverToggleSourcePhases
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverThreeReturnProbability
public import PottsContinuity.FKC.FiniteFK.ParafermionicModifiedPhaseAlgebra
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

/-- Actual atomic defects cancel under a closed two-return edge toggle as an
algebraic relation; this does not assert the corresponding probability-mass
relation. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_toggle_closed_return_two
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
        (toggleEdgeConfiguration e A) +
      (loopWeight q : ℂ) * parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A = 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  let u := parafermionicModifiedPhase q
  have hroute := parafermionicCoverFiniteEdgeCutClosedTwoToggleRoutingIndices
    n hn A e hclosed hπ0 hπ1
  have hi : i ≠ 0 := by simpa [π, i] using hπ0
  have hA0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 = i := by
    simpa [π, i] using hroute.1
  have hAi : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = 0 := by
    simpa [π, i] using hroute.2.1
  have hT0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 = j := by
    simpa [π, i, j] using hroute.2.2.1
  have hTj : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e j = i := by
    simpa [π, i, j] using hroute.2.2.2.1
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    rw [hA0]
    exact hi
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0 := by
    rw [hA0]
    exact hAi
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hT0]
    intro hz
    apply hi
    exact threeTerminalSwap.injective (by simpa [j, threeTerminalSwap_zero] using hz)
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
          (toggleEdgeConfiguration e A) e 0) ≠ 0 := by
    rw [hT0, hTj]
    exact hi
  have hDA := parafermionicCoverContourFiniteEdgeAtomicDefect_two_routing_factor
    q n hn A e h0A h1A
  have hDT := parafermionicCoverContourFiniteEdgeAtomicDefect_three_routing_factor
    q n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hphase := parafermionicCoverPathPhaseAtom_toggle_closed_return_two
    q n hn A e hclosed hπ0 hπ1
  have hDA' : parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      (u - 1) * parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
    simpa [u, parafermionicModifiedPhase, hclosed, hA0] using hDA
  have hDT' : parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
      (toggleEdgeConfiguration e A) =
      (u⁻¹ - 1) * (parafermionicCoverPathPhaseAtom q n hn
          (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 +
        parafermionicCoverPathPhaseAtom q n hn
          (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [u, parafermionicModifiedPhase, Complex.exp_neg, hT0, hTj,
      show e ∈ toggleEdgeConfiguration e A from by simp [toggleEdgeConfiguration, hclosed]] using hDT
  have hphase' :
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 ∧
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
        u ^ 2 * parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
    simpa [u, π, i, j] using hphase
  have hquad : u ^ 2 + 1 = (loopWeight q : ℂ) * u := by
    simpa [u] using parafermionicModifiedPhase_quadratic q
  have hu : u ≠ 0 := by simpa [u] using parafermionicModifiedPhase_ne_zero q
  calc
    _ = (u⁻¹ - 1) * (u ^ 2 + 1) *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 +
        (loopWeight q : ℂ) * (u - 1) *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
      rw [hDT', hDA', hphase'.1, hphase'.2]
      ring
    _ = 0 := by
      rw [hquad]
      field_simp [hu]
      ring

/-- Actual atomic defects cancel under a closed three-return edge toggle with
the critical FK edge odds. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_toggle_closed_return_three
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (loopWeight q : ℂ) * parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
        (toggleEdgeConfiguration e A) = 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := π i
  let u := parafermionicModifiedPhase q
  have hroute := parafermionicCoverFiniteEdgeCutClosedThreeToggleRoutingIndices
    n hn A e hclosed hπ0 hπ1
  have hA0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 = i := by
    simpa [π, i] using hroute.1
  have hAi : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = j := by
    simpa [π, i, j] using hroute.2.1
  have hAj : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e j = 0 := by
    simpa [π, i, j] using hroute.2.2.1
  have hT0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 = j := by
    simpa [π, i, j] using hroute.2.2.2.1
  have hTj : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e j = 0 := by
    simpa [π, i, j] using hroute.2.2.2.2
  have hi : i ≠ 0 := by simpa [π, i] using hπ0
  have hj : j ≠ 0 := by simpa [π, i, j] using hπ1
  have h0A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0 := by
    rw [hA0]
    exact hi
  have h1A : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0 := by
    rw [hA0, hAi]
    exact hj
  have h0T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e 0 ≠ 0 := by
    rw [hT0]
    exact hj
  have h1T : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
      (toggleEdgeConfiguration e A) e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn
          (toggleEdgeConfiguration e A) e 0) = 0 := by
    rw [hT0, hTj]
  have hDA := parafermionicCoverContourFiniteEdgeAtomicDefect_three_routing_factor
    q n hn A e h0A h1A
  have hDT := parafermionicCoverContourFiniteEdgeAtomicDefect_two_routing_factor
    q n hn (toggleEdgeConfiguration e A) e h0T h1T
  have hphase := parafermionicCoverPathPhaseAtom_toggle_closed_return_three
    q n hn A e hclosed hπ0 hπ1
  have hDA' : parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      (u - 1) * (parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 +
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1) := by
    simpa [u, parafermionicModifiedPhase, hclosed, hA0, hAi] using hDA
  have hDT' : parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
      (toggleEdgeConfiguration e A) =
      (u⁻¹ - 1) * parafermionicCoverPathPhaseAtom q n hn
        (toggleEdgeConfiguration e A)
        (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 := by
    simpa [u, parafermionicModifiedPhase, Complex.exp_neg, hT0, hTj,
      show e ∈ toggleEdgeConfiguration e A from by simp [toggleEdgeConfiguration, hclosed]] using hDT
  have hphase' :
      parafermionicCoverPathPhaseAtom q n hn (toggleEdgeConfiguration e A)
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 =
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 ∧
      parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 =
        u⁻¹ ^ 2 * parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 := by
    simpa [u, π, i, j] using hphase
  have hsum : u + u⁻¹ = (loopWeight q : ℂ) := by
    simpa [u] using parafermionicModifiedPhase_add_inv q
  have hquad : u ^ 2 + 1 = (loopWeight q : ℂ) * u := by
    simpa [u] using parafermionicModifiedPhase_quadratic q
  have hu : u ≠ 0 := by simpa [u] using parafermionicModifiedPhase_ne_zero q
  have hscaled : u⁻¹ ^ 2 + 1 = (loopWeight q : ℂ) * u⁻¹ := by
    have hmul : (u ^ 2 + 1) * u⁻¹ ^ 2 = u⁻¹ ^ 2 + 1 := by
      field_simp [hu]
      ring
    rw [← hmul, hquad]
    field_simp [hu]
  calc
    _ = (u - 1) * (u⁻¹ ^ 2 + 1) *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 +
        (loopWeight q : ℂ) * (u⁻¹ - 1) *
          parafermionicCoverPathPhaseAtom q n hn A
            (parafermionicCoverFiniteEdgeCutSourceLabels n hn e j).1.1 := by
      rw [hDA', hDT', hphase'.1, hphase'.2]
      ring
    _ = 0 := by
      rw [hscaled]
      field_simp [hu]
      ring

/-- The actual three-return cancellation also holds with the two genuine
finite FK configuration masses. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_three_return_probability_pair_cancel
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) ≠ 0) :
    (configurationProbability (ParafermionicAmbientGraph n) q ξ A : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (configurationProbability (ParafermionicAmbientGraph n) q ξ
        (toggleEdgeConfiguration e A) : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
          (toggleEdgeConfiguration e A) = 0 := by
  have hprob := parafermionicCoverFiniteEdgeCutThreeReturn_toggle_probability
    n hn q ξ A e hclosed hπ0 hπ1
  have hprob' : (configurationProbability (ParafermionicAmbientGraph n) q ξ
      (toggleEdgeConfiguration e A) : ℂ) =
      (loopWeight q : ℂ) *
        (configurationProbability (ParafermionicAmbientGraph n) q ξ A : ℂ) := by
    exact_mod_cast hprob
  have hdef := parafermionicCoverContourFiniteEdgeAtomicDefect_toggle_closed_return_three
    q n hn A e hclosed hπ0 hπ1
  calc
    _ = (configurationProbability (ParafermionicAmbientGraph n) q ξ A : ℂ) *
        (parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
          (loopWeight q : ℂ) * parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
            (toggleEdgeConfiguration e A)) := by
      rw [hprob']
      ring
    _ = 0 := by rw [hdef]; simp
