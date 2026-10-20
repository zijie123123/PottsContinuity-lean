module

public import PottsContinuity.PD.Duality.ConnectionSymmetry
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite
noncomputable section

/-- The original open graph transports along every lattice graph isomorphism. -/
def rcOpenConfigurationIso (e : PD.squareLattice ≃g PD.squareLattice) (ω : LatticeConfiguration) :
    PD.rcInfiniteOpenGraph ω ≃g PD.rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph e ω) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph,← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
    exact (wholePlaneOpenGraphIso e ω).map_rel_iff'

@[simp] theorem rcOpenConfigurationIso_apply (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) (v : LatticeVertex) : rcOpenConfigurationIso e ω v = e v := rfl

/-- Infinite-component membership is preserved by every graph isomorphism. -/
theorem graphIso_infinite_component_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u : V) :
    {v | H.Reachable (e u) v}.Infinite ↔ {v | G.Reachable u v}.Infinite := by
  constructor
  · intro hi hf
    apply hi
    apply (hf.image e).subset
    intro v hv
    refine ⟨e.symm v,?_,e.apply_symm_apply v⟩
    change G.Reachable u (e.symm v)
    simpa only [e.symm_apply_apply] using (e.symm.reachable_iff.mpr hv)
  · intro hi hf
    apply hi
    apply (hf.image e.symm).subset
    intro v hv
    refine ⟨e v,e.reachable_iff.mpr hv,e.symm_apply_apply v⟩

/-- Actual infinite membership has the same geometric transport as original edges. -/
theorem infiniteAt_configurationIso_iff (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) (u : LatticeVertex) :
    latticeConfigurationIsoHomeomorph e ω ∈ infiniteAt (e u) ↔ ω ∈ infiniteAt u := by
  exact graphIso_infinite_component_iff (rcOpenConfigurationIso e ω) u

theorem atMostOneInfiniteCluster_configurationIso_iff (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) :
    atMostOneInfiniteCluster (latticeConfigurationIsoHomeomorph e ω) ↔ atMostOneInfiniteCluster ω := by
  constructor
  · intro h u v hu hv
    apply (rcOpenConfigurationIso e ω).reachable_iff.mp
    exact h (e u) (e v) ((infiniteAt_configurationIso_iff e ω u).mpr hu)
      ((infiniteAt_configurationIso_iff e ω v).mpr hv)
  · intro h u v hu hv
    have he : e (e.symm u) = u := e.apply_symm_apply u
    have hf : e (e.symm v) = v := e.apply_symm_apply v
    rw [← he,← hf]
    apply (rcOpenConfigurationIso e ω).reachable_iff.mpr
    apply h
    · apply (infiniteAt_configurationIso_iff e ω _).mp
      rwa [he]
    · apply (infiniteAt_configurationIso_iff e ω _).mp
      rwa [hf]

theorem infiniteClusterEvent_configurationIso_iff (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph e ω ∈ infiniteClusterEvent ↔ ω ∈ infiniteClusterEvent := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨e.symm u,(infiniteAt_configurationIso_iff e ω _).mp ?_⟩
    rwa [e.apply_symm_apply]
  · rintro ⟨u,hu⟩
    exact ⟨e u,(infiniteAt_configurationIso_iff e ω u).mpr hu⟩

end
end PottsContinuity.PlanarTopology
