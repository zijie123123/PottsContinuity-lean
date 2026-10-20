-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverDefectConfigurationSum.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverContourEdgeSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTerminals
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservableSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeVisitClassification
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance defectConfigFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _
local instance defectEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance defectEdgeDecidable (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _
local instance defectFinitePortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := contourEdgePortFintype n
local instance defectInternalPortDecidable (n : ℕ) :
    DecidablePred (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverFinitePortOtherEndpointInBox n c) :=
  contourEdgeActualInternalDecidable n

/-- The pointwise edge defect is the actual signed sum over retained internal
port occurrences querying the given embedded finite edge. -/
def parafermionicCoverContourFiniteEdgeAtomicDefect
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) : ℂ := by
  classical
  exact ∑ c ∈ (Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e),
    (if parafermionicCoverIncomingPrimalLeft c.1.1 then (1 : ℂ) else -1) *
      parafermionicCoverPathPhaseAtom q n hn A (c.1, true)

/-- Finite expectation of an actual edge defect is the finite FK probability-weighted
sum of its literal pointwise atomic defects. -/
theorem parafermionicCoverContourFiniteEdgeDefect_eq_configuration_sum
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverContourFiniteEdgeDefect q n hn e =
      ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A := by
  classical
  unfold parafermionicCoverContourFiniteEdgeDefect
    parafermionicCoverContourFiniteEdgeAtomicDefect
  simp_rw [parafermionicCoverPathPhaseExpectation_eq_configuration_sum]
  calc
    (∑ c ∈ ((Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e)),
        (if parafermionicCoverIncomingPrimalLeft c.1.1 then (1 : ℂ) else -1) *
          ∑ A : Configuration (ParafermionicAmbientGraph n),
            (configurationProbability (ParafermionicAmbientGraph n) q
              (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
              parafermionicCoverPathPhaseAtom q n hn A (c.1, true)) =
      ∑ c ∈ ((Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e)), ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          ((if parafermionicCoverIncomingPrimalLeft c.1.1 then
              (1 : ℂ) else -1) *
            parafermionicCoverPathPhaseAtom q n hn A (c.1, true)) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        ring
    _ = ∑ A : Configuration (ParafermionicAmbientGraph n),
        ∑ c ∈ ((Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e)),
          (configurationProbability (ParafermionicAmbientGraph n) q
            (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
            ((if parafermionicCoverIncomingPrimalLeft c.1.1 then
                (1 : ℂ) else -1) *
              parafermionicCoverPathPhaseAtom q n hn A (c.1, true)) := by
        rw [Finset.sum_comm]
    _ = ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          (∑ c ∈ ((Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e)),
            (if parafermionicCoverIncomingPrimalLeft c.1.1 then (1 : ℂ) else -1) *
              parafermionicCoverPathPhaseAtom q n hn A (c.1, true)) := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]

/-- Reindexing by the actual edge flip averages the two configuration terms,
with the FK mass evaluated at each configuration that multiplies its atom. -/
theorem parafermionicCoverContourFiniteEdgeDefect_flip_pair_average
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverContourFiniteEdgeDefect q n hn e =
      (1 / 2 : ℂ) *
        ∑ A : Configuration (ParafermionicAmbientGraph n),
          ((configurationProbability (ParafermionicAmbientGraph n) q
              (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
              parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
            (configurationProbability (ParafermionicAmbientGraph n) q
              (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
              (toggleEdgeConfiguration e A) : ℂ) *
              parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
                (toggleEdgeConfiguration e A)) := by
  rw [parafermionicCoverContourFiniteEdgeDefect_eq_configuration_sum]
  exact sum_eq_average_toggle e (fun A =>
    (configurationProbability (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
      parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A)

/-- If the old exploration path makes no false-layer visit to the queried edge,
the actual atomic defect vanishes both before and after that edge is toggled. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_eq_zero_of_no_false_visit
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hno : ∀ c : ParafermionicCoverFinitePort n,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
        (c, false) ∉
          (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A = 0 ∧
      parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
        (toggleEdgeConfiguration e A) = 0 := by
  classical
  constructor
  · unfold parafermionicCoverContourFiniteEdgeAtomicDefect
    apply Finset.sum_eq_zero
    intro c hc
    have hquery := (Finset.mem_filter.mp hc).2
    have hzero := parafermionicCoverPathPhaseAtom_eq_zero_of_no_false_edge_visit
      q n hn A e hno c.1 hquery
    have htrue : parafermionicCoverPathPhaseAtom q n hn A (c.1, true) = 0 := by
      rw [← parafermionicCoverPathPhaseAtom_false_eq_true q n hn A c.1]
      exact hzero.1
    simp [htrue]
  · unfold parafermionicCoverContourFiniteEdgeAtomicDefect
    apply Finset.sum_eq_zero
    intro c hc
    have hquery := (Finset.mem_filter.mp hc).2
    have hzero := parafermionicCoverPathPhaseAtom_eq_zero_of_no_false_edge_visit
      q n hn A e hno c.1 hquery
    have htrue : parafermionicCoverPathPhaseAtom q n hn
        (toggleEdgeConfiguration e A) (c.1, true) = 0 := by
      rw [← parafermionicCoverPathPhaseAtom_false_eq_true q n hn
        (toggleEdgeConfiguration e A) c.1]
      exact hzero.2
    simp [htrue]

end
end PottsContinuity.FKC.FiniteFK
