-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/AdjacentBoundaryConnectionLowerBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnergy
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory
noncomputable section

/-- Lower bound for crossing a fixed present edge while connecting to a target
set. The FK measure and its boundary condition are unchanged. -/
theorem adjacent_boundary_connection_probability_lower_bound
    {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (q : ClusterWeight) (ξ : BoundaryCondition V) {u v : V}
    (huv : G.Adj u v) (T : Set V) :
    (1 / (1 + loopWeight q) : ℝ) *
        (measure G q ξ {A | ∃ z ∈ T, ActualConnected G A v z}).toReal ≤
      (measure G q ξ {A | ∃ z ∈ T, ActualConnected G A u z}).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr huv⟩
  let E : Set (Configuration G) := {A | e ∈ A}
  let Pv : Set (Configuration G) :=
    {A | ∃ z ∈ T, ActualConnected G A v z}
  let Pu : Set (Configuration G) :=
    {A | ∃ z ∈ T, ActualConnected G A u z}
  have hE : IsUpperSet E := by
    intro A B hAB hA
    exact hAB hA
  have hPv : IsUpperSet Pv := by
    intro A B hAB hA
    obtain ⟨z, hz, hconn⟩ := hA
    exact ⟨z, hz, actualConnected_mono hAB hconn⟩
  have hfinite := configurationProbability_edge_finite_energy q ξ Set.univ huv
    (by intro A; simp)
  have hEdge : (1 / (1 + loopWeight q) : ℝ) ≤ (measure G q ξ E).toReal := by
    have h := hfinite.1
    simpa [E, e, Set.univ_inter] using h
  have hAssoc := measure_positive_association q ξ E Pv hE hPv
  have hContain : E ∩ Pv ⊆ Pu := by
    intro A hA
    rcases hA with ⟨hopen, ⟨z, hz, hpath⟩⟩
    refine ⟨z, hz, ?_⟩
    have hadj : (openGraph G A).Adj u v := by
      apply (openGraph_adj G A u v).2
      exact ⟨e, hopen, rfl⟩
    exact (actualConnected_of_adj G A hadj).trans hpath
  have hmono : (measure G q ξ (E ∩ Pv)).toReal ≤ (measure G q ξ Pu).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hContain)
  have hconn_nonneg : 0 ≤ (measure G q ξ Pv).toReal := ENNReal.toReal_nonneg
  calc
    (1 / (1 + loopWeight q) : ℝ) * (measure G q ξ Pv).toReal
        ≤ (measure G q ξ E).toReal * (measure G q ξ Pv).toReal :=
          mul_le_mul_of_nonneg_right hEdge hconn_nonneg
    _ ≤ (measure G q ξ (E ∩ Pv)).toReal := hAssoc
    _ ≤ (measure G q ξ Pu).toReal := hmono

end
end PottsContinuity.FKC.FiniteFK
