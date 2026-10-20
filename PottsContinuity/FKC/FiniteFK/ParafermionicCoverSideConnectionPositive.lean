-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverSideConnectionPositive.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundarySums
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC MeasureTheory
noncomputable section

local instance coverSidePositiveEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance coverSidePositiveEdgeDecidable (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _
local instance coverSidePositiveConfigurationFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _
local instance coverSidePositiveConfigurationMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance coverSidePositiveConfigurationMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The positive vertical side point at height n is on the actual side
boundary in the sheet-zero interior. -/
theorem parafermionicCoverSideBoundary_positiveVertical_mem
    (n : ℕ) (hn : 1 ≤ n) :
    (((0 : ℤ), (n : ℤ)), (0 : ℤ)) ∈ parafermionicCoverExteriorNeighborBoundary n := by
  classical
  rw [parafermionicCoverExteriorNeighborBoundary, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · change (((0 : ℤ), (n : ℤ)), (0 : ℤ)) ∈ parafermionicCoverBoxVertices n
    rw [parafermionicCoverBoxVertices_mem]
    simp only
    have hnZ : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hn5Z : (0 : ℤ) ≤ ((n ^ 5 : ℕ) : ℤ) := by
      exact_mod_cast Nat.zero_le (n ^ 5)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · have hn5pos : 0 < ((n ^ 5 : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_pos (by omega : 0 < n)
    refine ⟨by omega, by omega, ?_⟩
    refine ⟨(((0 : ℤ), (n : ℤ) + 1), (0 : ℤ)), ?_, ?_⟩
    · apply (parafermionicCoverGraph_adj_iff_cases _ _).2
      exact Or.inl ⟨rfl, by ring, rfl⟩
    · change (((0 : ℤ), (n : ℤ) + 1), (0 : ℤ)) ∉
        parafermionicCoverBoxVertices n
      rw [parafermionicCoverBoxVertices_mem]
      simp only
      push_cast
      omega

/-- Under the actual free finite FK law, the same vertical side point has
positive origin-connection probability, witnessed by the all-open atom. -/
theorem parafermionicCoverSideBoundary_positiveVertical_connectionWeight
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight) :
    0 < parafermionicCoverBoxOriginConnectionWeight n q
      (((0 : ℤ), (n : ℤ)), (0 : ℤ)) := by
  classical
  let G := ParafermionicAmbientGraph n
  have hside := parafermionicCoverSideBoundary_positiveVertical_mem n hn
  have hbox : (((0 : ℤ), (n : ℤ)), (0 : ℤ)) ∈ parafermionicCoverBoxVertices n :=
    (Finset.mem_filter.mp hside).1
  let v : ParafermionicAmbientVertex n :=
    ⟨(((0 : ℤ), (n : ℤ)), (0 : ℤ)), hbox⟩
  let μ := (law G q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
  let E : Set (Configuration G) :=
    {A | ActualConnected G A (parafermionicCoverBoxOrigin n) v}
  let vert (k : ℕ) (hk : k ≤ n) : ParafermionicAmbientVertex n :=
    ⟨(((0 : ℤ), (k : ℤ)), (0 : ℤ)), by
      change (((0 : ℤ), (k : ℤ)), (0 : ℤ)) ∈ parafermionicCoverBoxVertices n
      rw [parafermionicCoverBoxVertices_mem]
      simp only
      push_cast
      have hnZ : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      have hkZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
      have hn5Z : (0 : ℤ) ≤ (n : ℤ) ^ 5 := by positivity
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩
  have hstart : parafermionicCoverBoxOrigin n = vert 0 (by omega) := by
    apply Subtype.ext
    rfl
  have hadj (k : ℕ) (hk : k + 1 ≤ n) : G.Adj (vert k (by omega)) (vert (k + 1) hk) := by
    change parafermionicCoverGraph.Adj _ _
    apply (parafermionicCoverGraph_adj_iff_cases _ _).2
    refine Or.inl ⟨rfl, ?_, rfl⟩
    norm_cast
  have hopenAdj {x y : ParafermionicAmbientVertex n} (hxy : G.Adj x y) :
      (openGraph G (Finset.univ : Configuration G)).Adj x y := by
    rw [openGraph_adj]
    change s(x, y) ∈ Subtype.val ''
      (↑(Finset.univ : Finset G.edgeSet) : Set G.edgeSet)
    refine ⟨⟨s(x, y), G.mem_edgeSet.mpr hxy⟩, Finset.mem_univ _, rfl⟩
  have hconn : ActualConnected G (Finset.univ : Configuration G)
      (parafermionicCoverBoxOrigin n) v := by
    have hreach : ∀ k (hk : k ≤ n),
        (openGraph G (Finset.univ : Configuration G)).Reachable
          (parafermionicCoverBoxOrigin n) (vert k hk) := by
      intro k
      induction k with
      | zero =>
          intro hk
          rw [hstart]
      | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          exact hprev.trans (hopenAdj (hadj k hk)).reachable
    simpa [v, vert, ActualConnected] using hreach n le_rfl
  have hsubset : ({(Finset.univ : Configuration G)} : Set (Configuration G)) ⊆ E := by
    rintro A rfl
    exact hconn
  have hmass := measure_mono (μ := μ) hsubset
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hmass
  have hsingle : (μ {(Finset.univ : Configuration G)}).toReal =
      configurationProbability G q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (Finset.univ : Configuration G) := by
    change (measure G q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
      {(Finset.univ : Configuration G)}).toReal = _
    rw [measure_singleton]
    exact ENNReal.toReal_ofReal
      (configurationProbability_pos G q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (Finset.univ : Configuration G)).le
  have hposAtom : 0 < (μ {(Finset.univ : Configuration G)}).toReal := by
    rw [hsingle]
    exact configurationProbability_pos G q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
      (Finset.univ : Configuration G)
  have hpositive : 0 < (μ E).toReal := hposAtom.trans_le hreal
  rw [parafermionicCoverBoxOriginConnectionWeight_subtype n q v]
  simpa [v, E, μ] using hpositive

end
end PottsContinuity.FKC.FiniteFK
