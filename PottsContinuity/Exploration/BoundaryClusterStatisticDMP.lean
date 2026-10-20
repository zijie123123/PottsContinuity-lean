module

public import PottsContinuity.Exploration.BoundaryClusterDMP
public import PottsContinuity.Exploration.CircuitFiberFreeComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.Exploration

open MeasureTheory
open PottsContinuity.PD.FK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance boundaryClusterStatisticEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundaryClusterStatisticEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance boundaryClusterStatisticConfigMeasurableSpace :
    MeasurableSpace (Configuration G) := ⊤
local instance boundaryClusterStatisticConfigMeasurableSingleton :
    MeasurableSingletonClass (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance boundaryClusterStatisticConfigNonempty : Nonempty (Configuration G) := ⟨∅⟩

/-- The selected boundary cluster record contains both its revealed edge set
and the states recorded on those edges. -/
def boundaryClusterStatistic (S : Set V) (C : Configuration G) :
    Configuration G × Configuration G :=
  (boundaryClusterRevealMap S C, C ∩ boundaryClusterRevealMap S C)

theorem boundaryClusterStatistic_fiber_eq_revealRecordEvent
    (S : Set V) (C : Configuration G) :
    {C' : Configuration G | boundaryClusterStatistic S C' =
        boundaryClusterStatistic S C} =
      revealRecordEvent (boundaryClusterRevealMap S) C := by
  ext C'
  constructor
  · intro h
    have hmap := congrArg Prod.fst h
    have hstates := congrArg Prod.snd h
    change boundaryClusterRevealMap S C' = boundaryClusterRevealMap S C at hmap
    change C' ∩ boundaryClusterRevealMap S C' =
      C ∩ boundaryClusterRevealMap S C at hstates
    refine ⟨hmap, ?_⟩
    rw [hmap] at hstates
    exact hstates
  · rintro ⟨hmap, hstates⟩
    apply Prod.ext
    · exact hmap
    · change C' ∩ boundaryClusterRevealMap S C' =
        C ∩ boundaryClusterRevealMap S C
      rw [hmap]
      exact hstates

theorem boundaryCluster_statistic_pullback_boundary_discrete
    (ξ : BoundaryCondition V) (S : Set V) (hboundary : ξ.boundary ⊆ S)
    (C : Configuration G) :
    ∀ x y : {v // v ∈ boundaryClusterInterior S C},
      (isolatedExtensionPullbackBoundary (boundaryClusterEmbedding S C)
        (frozenBoundary ξ
          (revealRecordConfiguration (boundaryClusterRevealMap S) C).val)).partition.r
        x y ↔ x = y := by
  let U := boundaryClusterInterior S C
  let K := revealRecordConfiguration (boundaryClusterRevealMap S) C
  have hdisjoint : Disjoint U ξ.boundary := by
    rw [Set.disjoint_left]
    intro x hxU hxboundary
    apply hxU
    exact ⟨x, hboundary hxboundary, by
      exact (SimpleGraph.reachable_iff_reflTransGen x x).2
        Relation.ReflTransGen.refl⟩
  have hnoedge : ∀ x, x ∈ U → ∀ y,
      ¬ (openGraph G K.val).Adj x y := by
    intro x hx y hxy
    exact boundaryCluster_revealed_open_no_incident S C hx hxy
  have houterFree {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
      (frozenBoundary ξ K.val).partition.r x y ↔ x = y :=
    frozenBoundary_partition_free_on_isolated ξ K.val U hdisjoint hnoedge hx hy
  intro x y
  change (frozenBoundary ξ K.val).partition.r
      (boundaryClusterEmbedding S C x) (boundaryClusterEmbedding S C y) ↔ x = y
  constructor
  · intro hxy
    exact Subtype.ext ((houterFree x.property y.property).mp hxy)
  · intro hxy
    exact (houterFree x.property y.property).mpr (congrArg Subtype.val hxy)

/-- Conditional probability comparison for an increasing event read from a
fixed finite reference graph. The boundary-cluster record is exposed in the
source graph; when its unreached interior embeds into the reference graph, the
conditional law there is bounded by the free law on that reference graph. -/
theorem finiteStatisticConditionalPMF_boundaryCluster_embeddedIncreasingEvent_le_freeGraph
    (θ : Parameters) (ξ : BoundaryCondition V) (S : Set V)
    (hboundary : ξ.boundary ⊆ S) (C : Configuration G)
    {Z : Type*} [Finite Z] {J : SimpleGraph Z}
    (g : {v // v ∈ boundaryClusterInterior S C} ↪ Z)
    (hGJ : (SimpleGraph.induce (boundaryClusterInterior S C) G).map g ≤ J)
    (ζ : BoundaryCondition Z)
    (A : Set (Configuration (SimpleGraph.induce (boundaryClusterInterior S C) G)))
    (hA : IsUpperSet A) :
    ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      (law G θ ξ) (fun D => (law_pos G θ ξ D).ne')
      (boundaryClusterStatistic S)
      ⟨boundaryClusterStatistic S C, ⟨C, rfl⟩⟩).toMeasure
      ((embeddedConfigurationRestriction
        (SimpleGraph.induce (boundaryClusterInterior S C) G) G
        (boundaryClusterEmbedding S C) (by
          intro x z hAdj
          obtain ⟨x', z', hadj, hx, hz⟩ :=
            (SimpleGraph.map_adj
              (f := boundaryClusterEmbedding S C)
              (G := SimpleGraph.induce (boundaryClusterInterior S C) G)
              x z).mp hAdj
          have hxval : (x' : V) = x := by
            simpa [boundaryClusterEmbedding] using hx
          have hzval : (z' : V) = z := by
            simpa [boundaryClusterEmbedding] using hz
          have h := (SimpleGraph.induce_adj (G := G)).mp hadj
          rw [hxval, hzval] at h
          exact h)) ⁻¹' A)).toReal ≤
      ((law J θ (BoundaryCondition.free ζ.boundary)).toMeasure
        ((embeddedConfigurationRestriction
          (SimpleGraph.induce (boundaryClusterInterior S C) G) J g hGJ) ⁻¹' A)).toReal := by
  let U := boundaryClusterInterior S C
  let H := SimpleGraph.induce U G
  let f := boundaryClusterEmbedding S C
  let K : RemovedConfiguration G (subgraphRemovedEdges (H.map f) G) :=
    revealRecordConfiguration (boundaryClusterRevealMap S) C
  let y : Set.range (boundaryClusterStatistic S) :=
    ⟨boundaryClusterStatistic S C, ⟨C, rfl⟩⟩
  have hGH : H.map f ≤ G := by
    intro x z hAdj
    obtain ⟨x', z', hadj, hx, hz⟩ :=
      (SimpleGraph.map_adj (f := f) (G := H) x z).mp hAdj
    have hxval : (x' : V) = x := by
      simpa [f, boundaryClusterEmbedding] using hx
    have hzval : (z' : V) = z := by
      simpa [f, boundaryClusterEmbedding] using hz
    have h := (SimpleGraph.induce_adj (G := G)).mp hadj
    rw [hxval, hzval] at h
    exact h
  have hfiber : {D : Configuration G | boundaryClusterStatistic S D = y.1} =
      frozenStateEvent (subgraphRemovedEdges (H.map f) G) K := by
    calc
      {D : Configuration G | boundaryClusterStatistic S D = y.1} =
          revealRecordEvent (boundaryClusterRevealMap S) C :=
        boundaryClusterStatistic_fiber_eq_revealRecordEvent S C
      _ = frozenStateEvent (boundaryClusterRevealMap S C)
          (revealRecordConfiguration (boundaryClusterRevealMap S) C) :=
        revealRecordEvent_eq_frozenStateEvent
          (boundaryClusterRevealMap S) (boundaryClusterRevealMap_stable S) C
      _ = frozenStateEvent (subgraphRemovedEdges (H.map f) G) K := rfl
  have hfree := boundaryCluster_statistic_pullback_boundary_discrete
    ξ S hboundary C
  have hfree' : ∀ x z : {v // v ∈ U},
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition.r
        x z ↔ x = z := by
    simpa [U, K, f] using hfree
  exact finiteStatisticConditionalPMF_embeddedIncreasingEvent_le_freeGraph_of_frozenFiber
    f hGH g hGJ ζ θ ξ (boundaryClusterStatistic S) y K hfiber hfree' A hA

end
end PottsContinuity.Exploration
