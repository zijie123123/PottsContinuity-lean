module

public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Opening original bonds preserves every actual open adjacency. -/
theorem rcOpenGraph_monotone : Monotone PD.rcInfiniteOpenGraph := by
  intro ω η hωη u v huv
  obtain ⟨he,ho⟩ := (rcInfiniteOpenGraph_adj ω u v).mp huv
  apply (rcInfiniteOpenGraph_adj η u v).mpr
  refine ⟨he,?_⟩
  have hh := hωη ⟨s(u,v),he⟩
  rw [ho] at hh
  exact top_le_iff.mp hh

/-- Infinite membership of a specified root is increasing. -/
theorem infiniteAt_isUpperSet (u : LatticeVertex) : IsUpperSet (infiniteAt u) := by
  intro ω η hωη hω
  apply hω.mono
  intro v hv
  exact SimpleGraph.Reachable.mono (rcOpenGraph_monotone hωη) hv

/-- A specified set intersects an infinite actual open component. -/
def infiniteHit (S : Set LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∃ u ∈ S, ω ∈ infiniteAt u}

theorem infiniteHit_isUpperSet (S : Set LatticeVertex) : IsUpperSet (infiniteHit S) := by
  rintro ω η hωη ⟨u,hu,hinf⟩
  exact ⟨u,hu,infiniteAt_isUpperSet u hωη hinf⟩

theorem infiniteHit_measurableSet (S : Set LatticeVertex) : MeasurableSet (infiniteHit S) := by
  have hm (u : LatticeVertex) : MeasurableSet {ω : LatticeConfiguration | u ∈ S ∧ ω ∈ infiniteAt u} := by
    by_cases hu : u ∈ S
    · simpa [hu] using measurableSet_infiniteAt u
    · simp [hu]
  convert MeasurableSet.iUnion hm using 1
  ext ω
  simp only [infiniteHit,Set.mem_ofPred_eq,Set.mem_iUnion]

end
end PottsContinuity.PlanarTopology
