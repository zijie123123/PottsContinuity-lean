module

public import PottsContinuity.PlanarTopology.LocalUniquenessEvents
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite Filter
noncomputable section

theorem finiteLocalUniquenessEvent_mono (S T U : Finset LatticeVertex) (hTU : T ⊆ U) :
    finiteLocalUniquenessEvent S T ⊆ finiteLocalUniquenessEvent S U := by
  rintro ω ⟨hST,hT⟩
  refine ⟨Finset.Subset.trans hST hTU,?_⟩
  intro u v hu hv hex hey
  let uT : {z // z ∈ T} := ⟨u.val,hST hu⟩
  let vT : {z // z ∈ T} := ⟨v.val,hST hv⟩
  have hconn := hT uT vT hu hv
    (by obtain ⟨x,hx,hreach⟩ := hex; exact ⟨x,fun hxT => hx (hTU hxT),hreach⟩)
    (by obtain ⟨y,hy,hreach⟩ := hey; exact ⟨y,fun hyT => hy (hTU hyT),hreach⟩)
  let e : (PD.rcInfiniteOpenGraph ω).induce (T : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph ω).induce (U : Set LatticeVertex) :=
    { toFun := fun z => ⟨z.val,hTU z.property⟩, map_rel' := fun h => h }
  exact hconn.map e

/-- Box exhaustion local uniqueness holds eventually for each actual
configuration having at most one infinite component, with all later boxes covered. -/
theorem unique_cluster_eventually_local_unique (ω : LatticeConfiguration)
    (hω : atMostOneInfiniteCluster ω) (S : Finset LatticeVertex) :
    ∀ᶠ n : ℕ in atTop, ω ∈ finiteLocalUniquenessEvent S (S ∪ latticeBox (0,0) n) := by
  obtain ⟨T,hT⟩ := unique_cluster_mem_finiteLocalUniquenessEvent ω hω S
  refine eventually_atTop.mpr ⟨subgraphBoxRadius T,?_⟩
  intro n hn
  apply finiteLocalUniquenessEvent_mono S T _ _ hT
  intro z hz
  exact Finset.mem_union_right _
    (latticeBox_mono (0,0) hn (subgraph_subset_boxRadius T hz))

/-- The local events form an increasing sequence along the same box exhaustion. -/
theorem finiteLocalUniquenessEvent_box_monotone (S : Finset LatticeVertex) :
    Monotone (fun n : ℕ => finiteLocalUniquenessEvent S (S ∪ latticeBox (0,0) n)) := by
  intro m n hmn
  apply finiteLocalUniquenessEvent_mono
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _ (latticeBox_mono (0,0) hmn hz)

end
end PottsContinuity.PlanarTopology
