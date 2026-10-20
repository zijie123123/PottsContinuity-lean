module

public import PottsContinuity.PlanarTopology.FiniteConnectionHull
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Actual cluster uniqueness localizes simultaneously in every domain containing
one finite witness set. No probability, regularity or box shape is assumed. -/
theorem unique_cluster_has_finite_local_witness (ω : LatticeConfiguration)
    (hω : atMostOneInfiniteCluster ω) (S : Finset LatticeVertex) :
    ∃ T : Finset LatticeVertex, S ⊆ T ∧
      ∀ D : Set LatticeVertex, (T : Set LatticeVertex) ⊆ D →
      ∀ u v : {z // z ∈ D}, u.val ∈ S → v.val ∈ S →
        (∃ x, x ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable u.val x) →
        (∃ y, y ∉ T ∧ (PD.rcInfiniteOpenGraph ω).Reachable v.val y) →
          ((PD.rcInfiniteOpenGraph ω).induce D).Reachable u v := by
  obtain ⟨T,hST,hT⟩ := exists_finite_local_uniqueness (PD.rcInfiniteOpenGraph ω) S
    (fun u v hu hv => hω u v hu hv)
  refine ⟨T,hST,?_⟩
  intro D hTD u v hu hv hex hey
  obtain ⟨p,hp⟩ := hT u.val hu v.val hv hex hey
  exact ⟨p.induce D (fun z hz => hTD (hp z hz))⟩

end
end PottsContinuity.PlanarTopology
