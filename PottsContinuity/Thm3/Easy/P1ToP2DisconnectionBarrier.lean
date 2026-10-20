module

public import PottsContinuity.Thm3.Easy.P1ToP2Conditional
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.Exploration.FrozenBoundaryFreeInterior
public import PottsContinuity.Exploration.CircuitFiberFreeComparison
public import PottsContinuity.Exploration.FiniteFiberComparison
public import PottsContinuity.Infinite.LocalComparisons

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open Filter
open Topology
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.Exploration

noncomputable section

local instance disconnectionEdgeFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) : Fintype G.edgeSet := Fintype.ofFinite _
local instance disconnectionEdgeDecidableEq {V : Type*} [Finite V]
    (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _
local instance disconnectionConfigurationMeasurableSpace {V : Type*}
    (G : SimpleGraph V) : MeasurableSpace (Configuration G) := ⊤
local instance disconnectionConfigurationMeasurableSingleton {V : Type*}
    (G : SimpleGraph V) : MeasurableSingletonClass (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance disconnectionConditionalMeasurableSpace {α : Type*} :
    MeasurableSpace α := ⊤
local instance disconnectionConditionalMeasurableSingleton {α : Type*} :
    MeasurableSingletonClass α :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

 def boundaryTouchCluster {V : Type*} {G : SimpleGraph V}
    (S : Set V) (C : Configuration G) : Set V :=
  {v | ∃ b, b ∈ S ∧ ActualConnected G C b v}

 def boundaryClusterInterior {V : Type*} {G : SimpleGraph V}
    (S : Set V) (C : Configuration G) : Set V :=
  (boundaryTouchCluster S C)ᶜ

 abbrev boundaryClusterEmbedding {V : Type*} {G : SimpleGraph V}
    (S : Set V) (C : Configuration G) :
    {v // v ∈ boundaryClusterInterior S C} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

 def boundaryClusterRevealEdges {V : Type*} [Finite V]
    {G : SimpleGraph V} (S : Set V) (C : Configuration G) : Configuration G :=
  subgraphRemovedEdges
    (SimpleGraph.map (boundaryClusterEmbedding S C)
      (SimpleGraph.induce (boundaryClusterInterior S C) G)) G

 def boundaryClusterRevealMap {V : Type*} [Finite V]
    {G : SimpleGraph V} (S : Set V) : RevealMap (G := G) :=
  boundaryClusterRevealEdges S

private theorem disconnection_openGraph_adj_iff_edge_mem
    {V : Type*} [Finite V] {G : SimpleGraph V} (C : Configuration G)
    {x y : V} (hxy : G.Adj x y) :
    (openGraph G C).Adj x y ↔
      (⟨s(x,y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∈ C := by
  rw [openGraph_adj]
  change s(x,y) ∈ Subtype.val '' (↑C : Set G.edgeSet) ↔ _
  constructor
  · rintro ⟨e, he, heval⟩
    have heq : e = ⟨s(x,y), G.mem_edgeSet.mpr hxy⟩ := Subtype.ext heval
    simpa [heq] using he
  · intro he
    exact ⟨⟨s(x,y), G.mem_edgeSet.mpr hxy⟩, he, rfl⟩

private theorem disconnection_revealed_edge_of_cluster
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (S : Set V) (C : Configuration G) {x y : V}
    (hx : x ∈ boundaryTouchCluster S C) (hxy : G.Adj x y) :
    (⟨s(x,y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∈
      boundaryClusterRevealEdges S C := by
  rw [boundaryClusterRevealEdges, mem_subgraphRemovedEdges]
  intro hmapped
  have hAdjMap :
      (SimpleGraph.map (boundaryClusterEmbedding S C)
        (SimpleGraph.induce (boundaryClusterInterior S C) G)).Adj x y :=
    (SimpleGraph.mem_edgeSet
      (SimpleGraph.map (boundaryClusterEmbedding S C)
        (SimpleGraph.induce (boundaryClusterInterior S C) G))).mp hmapped
  obtain ⟨x', y', hxy', hx', hy'⟩ :=
    (SimpleGraph.map_adj
      (f := boundaryClusterEmbedding S C)
      (G := SimpleGraph.induce (boundaryClusterInterior S C) G) x y).mp hAdjMap
  have hxnot' : (x' : V) ∉ boundaryTouchCluster S C := by
    simpa [boundaryClusterInterior] using x'.property
  have hxval : (x' : V) = x := by
    simpa [boundaryClusterEmbedding] using hx'
  exact hxnot' (hxval ▸ hx)

private theorem disconnection_boundaryTouchCluster_eq_of_agreement
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (S : Set V) (C C' : Configuration G)
    (hagree : C' ∩ boundaryClusterRevealMap S C =
      C ∩ boundaryClusterRevealMap S C) :
    boundaryTouchCluster S C = boundaryTouchCluster S C' := by
  have hstates (e : G.edgeSet) (he : e ∈ boundaryClusterRevealMap S C) :
      (e ∈ C ↔ e ∈ C') := by
    have hmem := congrArg (fun F : Configuration G => e ∈ F) hagree
    simp only [Finset.mem_inter] at hmem
    exact ⟨fun h => (hmem.mpr ⟨h, he⟩).1,
      fun h => (hmem.mp ⟨h, he⟩).1⟩
  apply Set.Subset.antisymm
  · intro v hv
    rcases hv with ⟨b, hb, hreach⟩
    refine ⟨b, hb, ?_⟩
    change (openGraph G C').Reachable b v
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have hpath : Relation.ReflTransGen (openGraph G C).Adj b v :=
      (SimpleGraph.reachable_iff_reflTransGen b v).mp hreach
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hprefix hxy ih =>
        have hprev : (openGraph G C).Reachable b x :=
          (SimpleGraph.reachable_iff_reflTransGen b x).2 hprefix
        have ih' : Relation.ReflTransGen (openGraph G C').Adj b x := ih hprev
        have hx : x ∈ boundaryTouchCluster S C := ⟨b, hb, hprev⟩
        have hxyG : G.Adj x y := (openGraph_le G C) hxy
        have hstate := disconnection_openGraph_adj_iff_edge_mem C hxyG
        have hstate' := disconnection_openGraph_adj_iff_edge_mem C' hxyG
        have he := hstate.mp hxy
        let e : G.edgeSet := ⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩
        have he' : e ∈ boundaryClusterRevealMap S C :=
          by simpa [e, boundaryClusterRevealMap] using
            disconnection_revealed_edge_of_cluster S C hx hxyG
        have heC : e ∈ C := by simpa [e] using he
        exact Relation.ReflTransGen.tail ih'
          (by simpa [e] using hstate'.mpr ((hstates e he').mp heC))
  · intro v hv
    rcases hv with ⟨b, hb, hreach⟩
    refine ⟨b, hb, ?_⟩
    change (openGraph G C).Reachable b v
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have hpath : Relation.ReflTransGen (openGraph G C').Adj b v :=
      (SimpleGraph.reachable_iff_reflTransGen b v).mp hreach
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hprefix hxy ih =>
        have hprev : (openGraph G C').Reachable b x :=
          (SimpleGraph.reachable_iff_reflTransGen b x).2 hprefix
        have ih' : Relation.ReflTransGen (openGraph G C).Adj b x := ih hprev
        have hprev : (openGraph G C).Reachable b x :=
          (SimpleGraph.reachable_iff_reflTransGen b x).2 ih'
        have hx : x ∈ boundaryTouchCluster S C := ⟨b, hb, hprev⟩
        have hxyG : G.Adj x y := (openGraph_le G C') hxy
        have hstate := disconnection_openGraph_adj_iff_edge_mem C hxyG
        have hstate' := disconnection_openGraph_adj_iff_edge_mem C' hxyG
        have he := hstate'.mp hxy
        let e : G.edgeSet := ⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩
        have he' : e ∈ boundaryClusterRevealMap S C :=
          by simpa [e, boundaryClusterRevealMap] using
            disconnection_revealed_edge_of_cluster S C hx hxyG
        have heC' : e ∈ C' := by simpa [e] using he
        exact Relation.ReflTransGen.tail ih'
          (by simpa [e] using hstate.mpr ((hstates e he').mpr heC'))

private theorem disconnection_boundaryClusterRevealMap_stable
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V) :
    ∀ C C' : Configuration G,
      C' ∩ boundaryClusterRevealMap S C = C ∩ boundaryClusterRevealMap S C →
      boundaryClusterRevealMap S C' = boundaryClusterRevealMap S C := by
  intro C C' hrecord
  have hagree : ∀ e ∈ boundaryClusterRevealEdges S C,
      (e ∈ C ↔ e ∈ C') := by
    intro e he
    constructor
    · intro hc
      have hmem : e ∈ C ∩ boundaryClusterRevealMap S C :=
        Finset.mem_inter.mpr ⟨hc, he⟩
      rw [← hrecord] at hmem
      exact (Finset.mem_inter.mp hmem).1
    · intro hc'
      have hmem : e ∈ C' ∩ boundaryClusterRevealMap S C :=
        Finset.mem_inter.mpr ⟨hc', he⟩
      rw [hrecord] at hmem
      exact (Finset.mem_inter.mp hmem).1
  have hcluster : boundaryTouchCluster S C' = boundaryTouchCluster S C :=
    (disconnection_boundaryTouchCluster_eq_of_agreement S C C' hrecord).symm
  change boundaryClusterRevealEdges S C' = boundaryClusterRevealEdges S C
  have hinterior : boundaryClusterInterior S C' = boundaryClusterInterior S C :=
    congrArg (fun A : Set V => Aᶜ) hcluster
  have hgraph :
      SimpleGraph.map (boundaryClusterEmbedding S C')
          (SimpleGraph.induce (boundaryClusterInterior S C') G) =
        SimpleGraph.map (boundaryClusterEmbedding S C)
          (SimpleGraph.induce (boundaryClusterInterior S C) G) := by
    ext x y
    constructor
    · intro hxy
      obtain ⟨x', y', hadj, hx', hy'⟩ :=
        (SimpleGraph.map_adj
          (f := boundaryClusterEmbedding S C')
          (G := SimpleGraph.induce (boundaryClusterInterior S C') G) x y).mp hxy
      have hxval : (x' : V) = x := by
        simpa [boundaryClusterEmbedding] using hx'
      have hyval : (y' : V) = y := by
        simpa [boundaryClusterEmbedding] using hy'
      have hxU : x ∈ boundaryClusterInterior S C :=
        hxval ▸ (hinterior ▸ x'.property)
      have hyU : y ∈ boundaryClusterInterior S C :=
        hyval ▸ (hinterior ▸ y'.property)
      have hxyG : G.Adj x y := by
        have h := (SimpleGraph.induce_adj (G := G)).mp hadj
        rw [← hxval, ← hyval]
        exact h
      exact (SimpleGraph.map_adj
        (f := boundaryClusterEmbedding S C)
        (G := SimpleGraph.induce (boundaryClusterInterior S C) G) x y).mpr
        ⟨⟨x, hxU⟩, ⟨y, hyU⟩,
          (SimpleGraph.induce_adj (G := G)).2 hxyG, rfl, rfl⟩
    · intro hxy
      obtain ⟨x', y', hadj, hx', hy'⟩ :=
        (SimpleGraph.map_adj
          (f := boundaryClusterEmbedding S C)
          (G := SimpleGraph.induce (boundaryClusterInterior S C) G) x y).mp hxy
      have hxval : (x' : V) = x := by
        simpa [boundaryClusterEmbedding] using hx'
      have hyval : (y' : V) = y := by
        simpa [boundaryClusterEmbedding] using hy'
      have hxU : x ∈ boundaryClusterInterior S C' :=
        hxval ▸ (hinterior.symm ▸ x'.property)
      have hyU : y ∈ boundaryClusterInterior S C' :=
        hyval ▸ (hinterior.symm ▸ y'.property)
      have hxyG : G.Adj x y := by
        have h := (SimpleGraph.induce_adj (G := G)).mp hadj
        rw [← hxval, ← hyval]
        exact h
      exact (SimpleGraph.map_adj
        (f := boundaryClusterEmbedding S C')
        (G := SimpleGraph.induce (boundaryClusterInterior S C') G) x y).mpr
        ⟨⟨x, hxU⟩, ⟨y, hyU⟩,
          (SimpleGraph.induce_adj (G := G)).2 hxyG, rfl, rfl⟩
  unfold boundaryClusterRevealEdges
  rw [hgraph]

private theorem disconnection_interior_edge_not_revealed
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V)
    (C : Configuration G) {x y : V}
    (hx : x ∈ boundaryClusterInterior S C)
    (hy : y ∈ boundaryClusterInterior S C) (hxy : G.Adj x y) :
    (⟨s(x,y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∉
      boundaryClusterRevealEdges S C := by
  rw [boundaryClusterRevealEdges, mem_subgraphRemovedEdges]
  intro hnotmap
  have hAdjMap :
      (SimpleGraph.map (boundaryClusterEmbedding S C)
        (SimpleGraph.induce (boundaryClusterInterior S C) G)).Adj x y :=
    (SimpleGraph.map_adj
      (f := boundaryClusterEmbedding S C)
      (G := SimpleGraph.induce (boundaryClusterInterior S C) G) x y).mpr
      ⟨⟨x, hx⟩, ⟨y, hy⟩,
        (SimpleGraph.induce_adj (G := G)).2 hxy, rfl, rfl⟩
  exact hnotmap ((SimpleGraph.mem_edgeSet
    (SimpleGraph.map (boundaryClusterEmbedding S C)
      (SimpleGraph.induce (boundaryClusterInterior S C) G))).mpr hAdjMap)

private theorem disconnection_revealed_open_no_incident
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V)
    (C : Configuration G) {x y : V}
    (hx : x ∈ boundaryClusterInterior S C)
    (hxy : (openGraph G
      (revealRecordConfiguration (boundaryClusterRevealMap S) C).val).Adj x y) :
    False := by
  have hxyG : G.Adj x y := (openGraph_le G _) hxy
  have he := (disconnection_openGraph_adj_iff_edge_mem _ hxyG).mp hxy
  have hstate :
      (⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩ : G.edgeSet) ∈
        C ∩ boundaryClusterRevealEdges S C := by
    simpa [revealRecordConfiguration, boundaryClusterRevealMap] using he
  have hstate' := Finset.mem_inter.mp hstate
  have hycluster : y ∈ boundaryTouchCluster S C := by
    by_contra hy
    have hyU : y ∈ boundaryClusterInterior S C := by
      simpa [boundaryClusterInterior] using hy
    exact disconnection_interior_edge_not_revealed S C hx hyU hxyG hstate'.2
  have hopenC : (openGraph G C).Adj x y :=
    (disconnection_openGraph_adj_iff_edge_mem C hxyG).mpr hstate'.1
  have hxcluster : x ∈ boundaryTouchCluster S C := by
    rcases hycluster with ⟨b, hb, hby⟩
    exact ⟨b, hb, hby.trans hopenC.reachable.symm⟩
  exact hx (by simpa [boundaryClusterInterior] using hxcluster)

 def boundaryClusterStatistic
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V)
    (C : Configuration G) : Configuration G × Configuration G :=
  (boundaryClusterRevealMap S C, C ∩ boundaryClusterRevealMap S C)

def disconnectionExteriorSeeds (M N : ℕ) :
    Set (BoxVertex (0, 0) N) :=
  {v | v.val ∉ latticeBox (0, 0) M}

private theorem disconnection_boundaryClusterStatistic_fiber
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V)
    (C : Configuration G) :
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

private theorem disconnection_boundaryClusterInterior_eq_of_stat
    {V : Type*} [Finite V] {G : SimpleGraph V} (S : Set V)
    (C C' : Configuration G)
    (hstat : boundaryClusterStatistic S C = boundaryClusterStatistic S C') :
    boundaryClusterInterior S C = boundaryClusterInterior S C' := by
  have hmap : boundaryClusterRevealMap S C = boundaryClusterRevealMap S C' :=
    congrArg Prod.fst hstat
  have hstates : C ∩ boundaryClusterRevealMap S C =
      C' ∩ boundaryClusterRevealMap S C' := congrArg Prod.snd hstat
  have hagree : C' ∩ boundaryClusterRevealMap S C =
      C ∩ boundaryClusterRevealMap S C := by
    rw [← hmap] at hstates
    exact hstates.symm
  have hcluster :=
    disconnection_boundaryTouchCluster_eq_of_agreement S C C' hagree
  simp [boundaryClusterInterior, hcluster]

private theorem disconnection_boundaryCluster_pullback_boundary_discrete
    {V : Type*} [Finite V] {G : SimpleGraph V}
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
    exact ⟨x, hboundary hxboundary,
      (SimpleGraph.reachable_iff_reflTransGen x x).2
        Relation.ReflTransGen.refl⟩
  have hnoedge : ∀ x, x ∈ U → ∀ y,
      ¬ (openGraph G K.val).Adj x y := by
    intro x hx y hxy
    exact disconnection_revealed_open_no_incident S C hx hxy
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

private theorem disconnection_boxGraph_openGraph_eq (N : ℕ)
    (C : Configuration (boxGraph (0, 0) N)) :
    openGraph (boxGraph (0, 0) N) C =
      boxOpenGraph (boxExtension 1 (0, 0) N C) N := by
  ext x y
  constructor
  · intro hxy
    have hxyG : (boxGraph (0, 0) N).Adj x y := (openGraph_le _ _) hxy
    have hglobal : squareLattice.Adj (x : LatticeVertex) (y : LatticeVertex) :=
      (boxGraph_adj_iff (0, 0) N x y).mp hxyG
    have hglobalEdge : s((x : BoxVertex (0, 0) N).val,
        (y : BoxVertex (0, 0) N).val) ∈
        PottsContinuity.PD.FK.squareLattice.edgeSet :=
      PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr hglobal
    let e : (boxGraph (0, 0) N).edgeSet := ⟨s(x,y), hxyG⟩
    have he : e ∈ C :=
      (disconnection_openGraph_adj_iff_edge_mem C hxyG).mp hxy
    have heq : boxEdgeEmbedding (0, 0) N e =
        (⟨s((x : BoxVertex (0, 0) N).val,
          (y : BoxVertex (0, 0) N).val),
          hglobalEdge⟩ : PottsContinuity.PD.FK.squareLattice.edgeSet) := by
      apply Subtype.ext
      rfl
    have hstateGlobal :
        boxExtension 1 (0, 0) N C
          ⟨s((x : BoxVertex (0, 0) N).val,
            (y : BoxVertex (0, 0) N).val),
            hglobalEdge⟩ = true := by
      rw [← heq]
      rw [boxExtension_at]
      exact decide_eq_true he
    exact (rcInfiniteOpenGraph_adj (boxExtension 1 (0, 0) N C)
      x.val y.val).mpr ⟨hglobal, hstateGlobal⟩
  · intro hxy
    have hglobal := (rcInfiniteOpenGraph_adj
      (boxExtension 1 (0, 0) N C) x.val y.val).mp hxy
    have hfinite : (boxGraph (0, 0) N).Adj x y :=
      (boxGraph_adj_iff (0, 0) N x y).mpr
        (PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mp hglobal.1)
    let e : (boxGraph (0, 0) N).edgeSet := ⟨s(x,y), hfinite⟩
    have heq : boxEdgeEmbedding (0, 0) N e =
        (⟨s((x : BoxVertex (0, 0) N).val,
          (y : BoxVertex (0, 0) N).val),
          hglobal.1⟩ : PottsContinuity.PD.FK.squareLattice.edgeSet) := by
      apply Subtype.ext
      rfl
    have hstate : decide (e ∈ C) = true := by
      have hopen := hglobal.2
      rw [← heq] at hopen
      simpa only [boxExtension_at] using hopen
    have he : e ∈ C := of_decide_eq_true hstate
    exact (disconnection_openGraph_adj_iff_edge_mem C hfinite).mpr he

private theorem int_bounds_of_natAbs_le {z : ℤ} {r : ℕ}
    (h : z.natAbs ≤ r) : -(r : ℤ) ≤ z ∧ z ≤ (r : ℤ) := by
  have hnat : z.natAbs ≤ (r : ℤ).natAbs := by simpa using h
  have hsq : z * z ≤ (r : ℤ) * (r : ℤ) :=
    Int.natAbs_le_iff_mul_self_le.mp hnat
  constructor
  · by_contra hnot
    have hlt : z < -(r : ℤ) := by omega
    have hleft : 0 < -z - (r : ℤ) := by omega
    have hright : 0 < -z + (r : ℤ) := by omega
    nlinarith [mul_pos hleft hright]
  · by_contra hnot
    have hlt : (r : ℤ) < z := by omega
    have hleft : 0 < z - (r : ℤ) := by omega
    have hright : 0 < z + (r : ℤ) := by omega
    nlinarith [mul_pos hleft hright]

private theorem latticeVertex_in_some_box (x : LatticeVertex) :
    ∃ n, x ∈ latticeBox (0, 0) n := by
  let n := max x.1.natAbs x.2.natAbs
  have hx := int_bounds_of_natAbs_le (z := x.1) (r := n) (Nat.le_max_left _ _)
  have hy := int_bounds_of_natAbs_le (z := x.2) (r := n) (Nat.le_max_right _ _)
  refine ⟨n, ?_⟩
  rw [mem_latticeBox]
  exact ⟨by simpa using hx, by simpa using hy⟩

private theorem finite_vertex_set_subset_box {S : Set LatticeVertex}
    (hS : S.Finite) : ∃ n, S ⊆ latticeBox (0, 0) n := by
  have hcover (x : LatticeVertex) : ∃ n, x ∈ latticeBox (0, 0) n :=
    latticeVertex_in_some_box x
  have heventually : ∀ᶠ n : ℕ in atTop, ∀ x ∈ S, x ∈ latticeBox (0, 0) n := by
    apply hS.eventually_all.mpr
    intro x hx
    obtain ⟨N, hN⟩ := hcover x
    filter_upwards [eventually_ge_atTop N] with n hn
    exact latticeBox_mono (0, 0) hn hN
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨n, hn⟩

def boxOpenGraph_hom_global (ω : LatticeConfiguration) (n : ℕ) :
    (boxOpenGraph ω n).Hom (rcInfiniteOpenGraph ω) := {
  toFun := fun v => v.val
  map_rel' := by
    intro a b hab
    apply (rcInfiniteOpenGraph_adj ω a.val b.val).2
    simpa [squareLattice, rcInfiniteOpenGraph] using
      (SimpleGraph.induce_adj.mp hab).1
}

/-- There is no open connection inside the induced outer box from the inner
box to the vertex boundary of the outer box. -/
def disconnectionBarrier (k M : ℕ) : Set LatticeConfiguration :=
  {ω | k ≤ M ∧ ∀ (x : LatticeVertex) (_hxk : x ∈ latticeBox (0, 0) k)
    (hxM : x ∈ latticeBox (0, 0) M) (y : BoxVertex (0, 0) M)
    (_hy : y.val ∈ PottsContinuity.PD.vertexBoundary
      (latticeBox (0, 0) M)),
      ¬ (boxOpenGraph ω M).Reachable ⟨x, hxM⟩ y}

private theorem disconnection_innerBox_unreached
    (k M N : ℕ) (hkM : k ≤ M)
    (C : Configuration (boxGraph (0, 0) N))
    (hbarrier : boxExtension 1 (0, 0) N C ∈ disconnectionBarrier k M)
    (x : BoxVertex (0, 0) N) (hxk : x.val ∈ latticeBox (0, 0) k) :
    x ∈ boundaryClusterInterior (disconnectionExteriorSeeds M N) C := by
  change x ∉ boundaryTouchCluster (disconnectionExteriorSeeds M N) C
  intro hxcluster
  rcases hxcluster with ⟨b, hb, hconnect⟩
  have hbout : b.val ∉ latticeBox (0, 0) M := hb
  obtain ⟨path⟩ :=
    (actualConnected_iff_walk (boxGraph (0, 0) N) C b x).mp hconnect
  have hxM : x.val ∈ latticeBox (0, 0) M :=
    latticeBox_mono (0, 0) hkM hxk
  let ω := boxExtension 1 (0, 0) N C
  have hwalk : (rcInfiniteOpenGraph ω).Walk x.val b.val := by
    rw [disconnection_boxGraph_openGraph_eq N C] at path
    let f := boxOpenGraph_hom_global ω N
    have hstart : f b = b.val := rfl
    have hend : f x = x.val := rfl
    rw [← hstart, ← hend]
    exact path.map f |>.reverse
  obtain ⟨z, hzM, pfx, hpfx, y, hzy, hyout⟩ :=
    walk_prefix_to_boundary hwalk hxM hbout
  have hzboundary : z ∈ PottsContinuity.PD.vertexBoundary
      (latticeBox (0, 0) M) := by
    refine ⟨hzM, y, ?_, hyout⟩
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω z y).mp hzy
    exact PottsContinuity.PD.squareLattice.mem_edgeSet.mp he
  have hpath := pfx.induce (latticeBox (0, 0) M : Set LatticeVertex) hpfx
  have hreach : (boxOpenGraph ω M).Reachable
      ⟨x.val, hxM⟩ ⟨z, hzM⟩ := hpath.reachable
  rcases hbarrier with ⟨_, hdisconnect⟩
  exact hdisconnect x.val hxk hxM ⟨z, hzM⟩ hzboundary hreach

private theorem disconnection_embeddedConfigurationEmbedding_mem
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hGH : G.map f ≤ H) (D : Configuration G) (e : G.edgeSet) :
    embeddedEdgeEmbedding G H f hGH e ∈
        embeddedConfigurationEmbedding G H f hGH D ↔ e ∈ D := by
  rw [embeddedConfigurationEmbedding_eq_map]
  simp

private theorem disconnection_boxExtension_mono
    (i : Fin 2) (c : LatticeVertex) (r : ℕ) :
    Monotone (boxExtension i c r) := by
  intro C D hCD e
  by_cases he : e ∈ boxEdges c r
  · obtain ⟨f, hf⟩ := he
    rw [← hf, boxExtension_at, boxExtension_at]
    by_cases hC : f ∈ C
    · have hD := hCD hC
      simp [hC, hD]
    · simp [hC]
  · fin_cases i
    · simp [boxExtension, boxConfiguration_outside c r C e he,
        boxConfiguration_outside c r D e he]
    · simp [boxExtension, wiredBoxConfiguration_outside c r C e he,
        wiredBoxConfiguration_outside c r D e he]

private theorem disconnection_embeddedConfigurationEmbedding_mono
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hGH : G.map f ≤ H) :
    Monotone (embeddedConfigurationEmbedding G H f hGH) := by
  intro C D hCD
  rw [embeddedConfigurationEmbedding_eq_map, embeddedConfigurationEmbedding_eq_map]
  exact Finset.map_subset_map.mpr hCD

private theorem disconnection_conditionalEventProbability_eq
    {α β : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (hp : ∀ a, p a ≠ 0) (record : α → β)
    (y : Set.range record) (E F : Set α)
    (heq : ∀ a, record a = y.1 → (a ∈ E ↔ a ∈ F)) :
    ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      p hp record y).toMeasure E).toReal =
    ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
      p hp record y).toMeasure F).toReal := by
  let ν := PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
    p hp record y
  have hsupp (a : α) (ha : a ∈ ν.support) : record a = y.1 := by
    have hfilter : a ∈ {a | record a = y.1} ∧ a ∈ p.support := by
      simpa [ν, PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF,
        PMF.mem_support_filter_iff] using ha
    exact hfilter.1
  have hsets : E ∩ ν.support = F ∩ ν.support := by
    ext a
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨ha, hs⟩
      exact ⟨(heq a (hsupp a hs)).mp ha, hs⟩
    · rintro ⟨ha, hs⟩
      exact ⟨(heq a (hsupp a hs)).mpr ha, hs⟩
  have hmeasure := ν.toMeasure_apply_eq_of_inter_support_eq
    (MeasurableSet.of_discrete (s := E))
    (MeasurableSet.of_discrete (s := F)) hsets
  exact congrArg ENNReal.toReal hmeasure

private theorem disconnection_boxEdge_has_interior_preimage
    (k N : ℕ) (hbox : latticeBox (0, 0) k ⊆ latticeBox (0, 0) N)
    (U : Set (BoxVertex (0, 0) N))
    (f : {v : BoxVertex (0, 0) N // v ∈ U} ↪ BoxVertex (0, 0) N)
    (hGH : (SimpleGraph.induce U (boxGraph (0, 0) N)).map f ≤
      boxGraph (0, 0) N)
    (hInner : ∀ x : BoxVertex (0, 0) k,
      boxVertexEmbedding hbox x ∈ U)
    (hF : ∀ x : {v : BoxVertex (0, 0) N // v ∈ U}, f x = x.val)
    (e : (boxGraph (0, 0) k).edgeSet) :
    ∃ eG : (SimpleGraph.induce U (boxGraph (0, 0) N)).edgeSet,
      boxEdgeEmbedding (0, 0) N
          (embeddedEdgeEmbedding (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH eG) =
        boxEdgeEmbedding (0, 0) k e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxyK : (boxGraph (0, 0) k).Adj x y :=
      (boxGraph (0, 0) k).mem_edgeSet.mp he
    have hxyH : (boxGraph (0, 0) N).Adj
        (boxVertexEmbedding hbox x) (boxVertexEmbedding hbox y) :=
      (boxGraph_map_boxVertexEmbedding hbox)
        ((SimpleGraph.map_adj (boxVertexEmbedding hbox)
          (boxGraph (0, 0) k) _ _).mpr ⟨x, y, hxyK, rfl, rfl⟩)
    let xG : {v : BoxVertex (0, 0) N // v ∈ U} :=
      ⟨boxVertexEmbedding hbox x, hInner x⟩
    let yG : {v : BoxVertex (0, 0) N // v ∈ U} :=
      ⟨boxVertexEmbedding hbox y, hInner y⟩
    have hxyG : (SimpleGraph.induce U (boxGraph (0, 0) N)).Adj xG yG :=
      (SimpleGraph.induce_adj (G := boxGraph (0, 0) N)).mpr hxyH
    let eG : (SimpleGraph.induce U (boxGraph (0, 0) N)).edgeSet :=
      ⟨s(xG, yG), hxyG⟩
    have hfx : f xG = boxVertexEmbedding hbox x := by
      simpa [xG] using hF xG
    have hfy : f yG = boxVertexEmbedding hbox y := by
      simpa [yG] using hF yG
    have hvalx : (f xG).val = x.val := by rw [hfx]; rfl
    have hvaly : (f yG).val = y.val := by rw [hfy]; rfl
    refine ⟨eG, ?_⟩
    apply Subtype.ext
    change Sym2.map (fun v : BoxVertex (0, 0) N => v.val)
        (Sym2.map f (s(xG, yG))) =
      Sym2.map (fun v : BoxVertex (0, 0) k => v.val) (s(x, y))
    rw [Sym2.map_map]
    change s((f xG).val, (f yG).val) = s(x.val, y.val)
    rw [hvalx, hvaly]

private theorem disconnection_innerExtension_event_iff
    (i : Fin 2) (k N : ℕ) (hbox : latticeBox (0, 0) k ⊆ latticeBox (0, 0) N)
    (U : Set (BoxVertex (0, 0) N))
    (f : {v : BoxVertex (0, 0) N // v ∈ U} ↪ BoxVertex (0, 0) N)
    (hGH : (SimpleGraph.induce U (boxGraph (0, 0) N)).map f ≤
      boxGraph (0, 0) N)
    (hInner : ∀ x : BoxVertex (0, 0) k,
      boxVertexEmbedding hbox x ∈ U)
    (hF : ∀ x : {v : BoxVertex (0, 0) N // v ∈ U}, f x = x.val)
    (D : Configuration (boxGraph (0, 0) N))
    {A : Set LatticeConfiguration}
    (hdep : DependsOn (boxEdges (0, 0) k) A) :
    (boxExtension i (0, 0) N D ∈ A) ↔
      boxExtension 0 (0, 0) N
        (embeddedConfigurationEmbedding
          (SimpleGraph.induce U (boxGraph (0, 0) N))
          (boxGraph (0, 0) N) f hGH
          (embeddedConfigurationRestriction
            (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH D)) ∈ A := by
  apply hdep
  intro e he
  obtain ⟨eK, heK⟩ := he
  let hmap : (boxGraph (0, 0) k).map
      (boxVertexEmbedding hbox) ≤ boxGraph (0, 0) N :=
    boxGraph_map_boxVertexEmbedding hbox
  obtain ⟨eG, hEdgeG⟩ :=
    disconnection_boxEdge_has_interior_preimage k N hbox U f hGH hInner hF eK
  have hEdgeK : boxEdgeEmbedding (0, 0) N
      (embeddedEdgeEmbedding (boxGraph (0, 0) k) (boxGraph (0, 0) N)
        (boxVertexEmbedding hbox) hmap eK) = boxEdgeEmbedding (0, 0) k eK :=
    boxEdgeEmbedding_compatible hbox eK
  have hEdge : embeddedEdgeEmbedding
      (SimpleGraph.induce U (boxGraph (0, 0) N)) (boxGraph (0, 0) N) f hGH eG =
      embeddedEdgeEmbedding (boxGraph (0, 0) k) (boxGraph (0, 0) N)
        (boxVertexEmbedding hbox) hmap eK := by
    apply (boxEdgeEmbedding (0, 0) N).injective
    calc
      boxEdgeEmbedding (0, 0) N
          (embeddedEdgeEmbedding
            (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH eG) = boxEdgeEmbedding (0, 0) k eK := hEdgeG
      _ = boxEdgeEmbedding (0, 0) N
          (embeddedEdgeEmbedding (boxGraph (0, 0) k) (boxGraph (0, 0) N)
            (boxVertexEmbedding hbox) hmap eK) := hEdgeK.symm
  have hstate :
      embeddedEdgeEmbedding (SimpleGraph.induce U (boxGraph (0, 0) N))
        (boxGraph (0, 0) N) f hGH eG ∈
        embeddedConfigurationEmbedding
          (SimpleGraph.induce U (boxGraph (0, 0) N))
          (boxGraph (0, 0) N) f hGH
          (embeddedConfigurationRestriction
            (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH D) ↔
      embeddedEdgeEmbedding (SimpleGraph.induce U (boxGraph (0, 0) N))
        (boxGraph (0, 0) N) f hGH eG ∈ D := by
    rw [disconnection_embeddedConfigurationEmbedding_mem,
      mem_embeddedConfigurationRestriction]
  have hstate' :
      embeddedEdgeEmbedding (boxGraph (0, 0) k) (boxGraph (0, 0) N)
        (boxVertexEmbedding hbox) hmap eK ∈
        embeddedConfigurationEmbedding
          (SimpleGraph.induce U (boxGraph (0, 0) N))
          (boxGraph (0, 0) N) f hGH
          (embeddedConfigurationRestriction
            (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH D) ↔
      embeddedEdgeEmbedding (boxGraph (0, 0) k) (boxGraph (0, 0) N)
        (boxVertexEmbedding hbox) hmap eK ∈ D := by
    simpa only [hEdge] using hstate
  have hstateBool :
      boxExtension i (0, 0) N D (boxEdgeEmbedding (0, 0) k eK) =
        boxExtension 0 (0, 0) N
          (embeddedConfigurationEmbedding
            (SimpleGraph.induce U (boxGraph (0, 0) N))
            (boxGraph (0, 0) N) f hGH
            (embeddedConfigurationRestriction
              (SimpleGraph.induce U (boxGraph (0, 0) N))
              (boxGraph (0, 0) N) f hGH D))
          (boxEdgeEmbedding (0, 0) k eK) := by
    rw [← hEdgeK]
    rw [boxExtension_at, boxExtension_at]
    exact Bool.eq_iff_iff.mpr (by simpa using hstate'.symm)
  rw [← heK]
  exact hstateBool

private theorem disconnection_boxOpenGraph_eq_of_agreement
    (M : ℕ) (ω η : LatticeConfiguration)
    (hagree : ∀ e ∈ boxEdges (0, 0) M, ω e = η e) :
    boxOpenGraph ω M = boxOpenGraph η M := by
  apply SimpleGraph.ext
  ext x y
  change (rcInfiniteOpenGraph ω).Adj x.val y.val ↔
    (rcInfiniteOpenGraph η).Adj x.val y.val
  constructor
  · intro hopen
    obtain ⟨he, hstate⟩ := (rcInfiniteOpenGraph_adj ω x.val y.val).mp hopen
    let e : PottsContinuity.PD.RCInfinite.Edge := ⟨s(x.val, y.val), he⟩
    have hbox : e ∈ boxEdges (0, 0) M := by
      rw [PottsContinuity.PD.RCInfinite.mem_boxEdges_iff]
      intro z hz
      rcases (Sym2.mem_iff').mp hz with hzx | hzy
      · rw [hzx]
        exact x.property
      · rw [hzy]
        exact y.property
    have hsame := hagree e hbox
    exact (rcInfiniteOpenGraph_adj η x.val y.val).mpr
      ⟨he, by rw [← hsame]; exact hstate⟩
  · intro hopen
    obtain ⟨he, hstate⟩ := (rcInfiniteOpenGraph_adj η x.val y.val).mp hopen
    let e : PottsContinuity.PD.RCInfinite.Edge := ⟨s(x.val, y.val), he⟩
    have hbox : e ∈ boxEdges (0, 0) M := by
      rw [PottsContinuity.PD.RCInfinite.mem_boxEdges_iff]
      intro z hz
      rcases (Sym2.mem_iff').mp hz with hzx | hzy
      · rw [hzx]
        exact x.property
      · rw [hzy]
        exact y.property
    have hsame := hagree e hbox
    exact (rcInfiniteOpenGraph_adj ω x.val y.val).mpr
      ⟨he, by rw [hsame]; exact hstate⟩

/-- The disconnection event only reads edges of its outer induced box. -/
theorem disconnectionBarrier_dependsOn (k M : ℕ) :
    DependsOn (boxEdges (0, 0) M) (disconnectionBarrier k M) := by
  intro ω η hagree
  have hgraph := disconnection_boxOpenGraph_eq_of_agreement M ω η hagree
  constructor
  · rintro ⟨hkM, h⟩
    refine ⟨hkM, ?_⟩
    intro x hxk hxM y hy
    rw [← hgraph]
    exact h x hxk hxM y hy
  · rintro ⟨hkM, h⟩
    refine ⟨hkM, ?_⟩
    intro x hxk hxM y hy
    rw [hgraph]
    exact h x hxk hxM y hy

/-- The disconnection event is a finite-coordinate event. -/
theorem disconnectionBarrier_isCylinder (k M : ℕ) :
    IsCylinder (disconnectionBarrier k M) := by
  classical
  have hfinite : (boxEdges (0, 0) M).Finite := by
    unfold boxEdges
    exact Set.finite_range _
  refine ⟨hfinite.toFinset, ?_⟩
  intro ω η hagree
  apply disconnectionBarrier_dependsOn k M ω η
  intro e he
  exact hagree e (hfinite.mem_toFinset.mpr he)

/-- The disconnection event is measurable. -/
theorem disconnectionBarrier_measurable (k M : ℕ) :
    MeasurableSet (disconnectionBarrier k M) :=
  (disconnectionBarrier_isCylinder k M).measurableSet

private theorem disconnection_wiredBox_comparison
    (θ : Parameters) (k M N : ℕ) (hkM : k ≤ M) (hMN : M < N)
    {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges (0, 0) k) A) (hupper : IsUpperSet A) :
    (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real A ≤
      (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A +
        (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real
          (disconnectionBarrier k M)ᶜ := by
  let hbox : latticeBox (0, 0) k ⊆ latticeBox (0, 0) N :=
    latticeBox_mono (0, 0) (hkM.trans hMN.le)
  let H := boxGraph (0, 0) N
  let ξ := boxBoundary 1 (0, 0) N
  let ext := boxExtension 1 (0, 0) N
  let S := disconnectionExteriorSeeds M N
  let record : Configuration H → Configuration H × Configuration H :=
    boundaryClusterStatistic S
  let good : Set (Configuration H) :=
    {C | ∀ x : BoxVertex (0, 0) k,
      boxVertexEmbedding hbox x ∈ boundaryClusterInterior S C}
  let event : Set (Configuration H) := ext ⁻¹' A
  have hbarrierGood (C : Configuration H)
      (hC : ext C ∈ disconnectionBarrier k M) : C ∈ good := by
    intro x
    exact disconnection_innerBox_unreached k M N hkM C hC
      (boxVertexEmbedding hbox x) x.property
  have hgoodStable : ∀ C D : Configuration H, record C = record D →
      (C ∈ good ↔ D ∈ good) := by
    intro C D hCD
    have hU := disconnection_boundaryClusterInterior_eq_of_stat S C D hCD
    change (∀ x : BoxVertex (0, 0) k,
        boxVertexEmbedding hbox x ∈ boundaryClusterInterior S C) ↔
      (∀ x : BoxVertex (0, 0) k,
        boxVertexEmbedding hbox x ∈ boundaryClusterInterior S D)
    rw [hU]
  have hbadSubset : goodᶜ ⊆ ext ⁻¹' (disconnectionBarrier k M)ᶜ := by
    intro C hC
    change ¬ C ∈ good at hC
    change ext C ∈ (disconnectionBarrier k M)ᶜ
    intro hbarrier
    exact hC (hbarrierGood C hbarrier)
  have hfreeReference :
      (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A ≤ 1 := by
    let ν := (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration)
    let : IsProbabilityMeasure ν := by
      dsimp [ν]
      infer_instance
    exact MeasureTheory.measureReal_mono (Set.subset_univ A) |>.trans (by
      simp [Measure.real])
  let p := law H θ ξ
  have hp : ∀ C : Configuration H, p C ≠ 0 := by
    intro C
    exact (law_pos H θ ξ C).ne'
  have hconditional : ∀ y : Set.range record,
      (∃ C : Configuration H, record C = y.1 ∧ C ∈ good) →
      ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
        p (fun C => (law_pos H θ ξ C).ne') record y).toMeasure event).toReal ≤
        (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A := by
    intro y hy
    obtain ⟨C₀, hC₀, hgood₀⟩ := hy
    let y₀ : Set.range record := ⟨record C₀, ⟨C₀, rfl⟩⟩
    have hy₀ : y = y₀ := Subtype.ext hC₀.symm
    subst y
    let U := boundaryClusterInterior S C₀
    let G := SimpleGraph.induce U H
    let f := boundaryClusterEmbedding S C₀
    have hGH : G.map f ≤ H := by
      intro x y hxy
      obtain ⟨x', y', hadj, hx', hy'⟩ :=
        (SimpleGraph.map_adj (f := f) (G := G) x y).mp hxy
      have hxval : (x' : BoxVertex (0, 0) N) = x := by
        simpa [f, boundaryClusterEmbedding] using hx'
      have hyval : (y' : BoxVertex (0, 0) N) = y := by
        simpa [f, boundaryClusterEmbedding] using hy'
      have h := (SimpleGraph.induce_adj (G := H)).mp hadj
      rw [hxval, hyval] at h
      exact h
    have hInner : ∀ x : BoxVertex (0, 0) k,
        boxVertexEmbedding hbox x ∈ U := by
      intro x
      simpa [U, good] using hgood₀ x
    have hf : ∀ x : {v : BoxVertex (0, 0) N // v ∈ U}, f x = x.val := by
      intro x
      rfl
    have hboundary : ξ.boundary ⊆ S := by
      intro v hv
      change v.val ∉ latticeBox (0, 0) M
      intro hvM
      have hcoord := box_boundary_coordinate_edge N hv
      rw [mem_latticeBox] at hvM
      rcases hcoord with hleft | hright | hbottom | htop <;> omega
    let K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H) :=
      revealRecordConfiguration (boundaryClusterRevealMap S) C₀
    have hfiber : {D : Configuration H | record D = y₀.1} =
        frozenStateEvent (subgraphRemovedEdges (G.map f) H) K := by
      calc
        {D : Configuration H | record D = y₀.1} =
            revealRecordEvent (boundaryClusterRevealMap S) C₀ :=
          disconnection_boundaryClusterStatistic_fiber S C₀
        _ = frozenStateEvent (boundaryClusterRevealMap S C₀)
            (revealRecordConfiguration (boundaryClusterRevealMap S) C₀) :=
          revealRecordEvent_eq_frozenStateEvent
            (boundaryClusterRevealMap S)
            (disconnection_boundaryClusterRevealMap_stable S) C₀
        _ = frozenStateEvent (subgraphRemovedEdges (G.map f) H) K := by
          rfl
    have hfree := disconnection_boundaryCluster_pullback_boundary_discrete
      ξ S hboundary C₀
    have hAInner : IsUpperSet
        (embeddedConfigurationEmbedding G H f hGH ⁻¹'
          ((boxExtension 0 (0, 0) N) ⁻¹' A)) := by
      intro D E hDE hD
      apply hupper
      · exact disconnection_boxExtension_mono 0 (0, 0) N
          (disconnection_embeddedConfigurationEmbedding_mono G H f hGH hDE)
      · exact hD
    let B : Set (Configuration G) :=
      (embeddedConfigurationEmbedding G H f hGH) ⁻¹'
        ((boxExtension 0 (0, 0) N) ⁻¹' A)
    have hB : IsUpperSet B := by
      simpa [B] using hAInner
    have hcond :=
      finiteStatisticConditionalPMF_embeddedIncreasingEvent_le_freeGraph_of_frozenFiber
        f hGH f hGH ξ θ ξ record y₀ K hfiber hfree B hB
    have hpre :
        (embeddedConfigurationRestriction G H f hGH) ⁻¹' B =
          (boxExtension 0 (0, 0) N) ⁻¹' A := by
      ext D
      change boxExtension 0 (0, 0) N
          (embeddedConfigurationEmbedding G H f hGH
            (embeddedConfigurationRestriction G H f hGH D)) ∈ A ↔
        boxExtension 0 (0, 0) N D ∈ A
      exact (disconnection_innerExtension_event_iff 0 k N hbox U f hGH
        hInner hf D hdep).symm
    have hfreeLaw : law H θ (BoundaryCondition.free ξ.boundary) =
        law H θ (BoundaryCondition.free ∅) := by
      apply law_eq_of_boundary_partition_eq
      rfl
    have hfreeProbability :
        ((law H θ (BoundaryCondition.free ξ.boundary)).toMeasure
          ((embeddedConfigurationRestriction G H f hGH) ⁻¹' B)).toReal =
        (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A := by
      rw [hpre, hfreeLaw]
      have hBox :
          (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A =
            ((law H θ (BoundaryCondition.free ∅)).toMeasure
              ((boxExtension 0 (0, 0) N) ⁻¹' A)).toReal := by
        have h := boxMeasure_apply θ 0 (0, 0) N hA.measurableSet
        simpa [Measure.real, boxBoundary,
          PottsContinuity.PD.FK.measure] using
          congrArg ENNReal.toReal h
      exact hBox.symm
    have hrecordGood : ∀ D : Configuration H,
        record D = y₀.1 → (D ∈ good ↔ C₀ ∈ good) := by
      intro D hD
      have hstat : record D = record C₀ := by
        dsimp [y₀] at hD
        exact hD
      have hU := disconnection_boundaryClusterInterior_eq_of_stat S D C₀ hstat
      change (∀ x : BoxVertex (0, 0) k,
          boxVertexEmbedding hbox x ∈ boundaryClusterInterior S D) ↔
        (∀ x : BoxVertex (0, 0) k,
          boxVertexEmbedding hbox x ∈ boundaryClusterInterior S C₀)
      rw [hU]
    have hEEq : ∀ D : Configuration H, record D = y₀.1 →
        (D ∈ event ↔ D ∈ (embeddedConfigurationRestriction G H f hGH) ⁻¹' B) := by
      intro D hD
      have hstat : record D = record C₀ := by
        dsimp [y₀] at hD
        exact hD
      have hU := disconnection_boundaryClusterInterior_eq_of_stat S D C₀ hstat
      have hDgood : D ∈ good := (hrecordGood D hD).mpr hgood₀
      have hInnerD : ∀ x : BoxVertex (0, 0) k,
          boxVertexEmbedding hbox x ∈ U := by
        intro x
        have hx := hDgood x
        simpa [U, good, hU] using hx
      change boxExtension 1 (0, 0) N D ∈ A ↔
        boxExtension 0 (0, 0) N
          (embeddedConfigurationEmbedding G H f hGH
            (embeddedConfigurationRestriction G H f hGH D)) ∈ A
      exact disconnection_innerExtension_event_iff 1 k N hbox U f hGH
        hInnerD hf D hdep
    have hconditionalEq := disconnection_conditionalEventProbability_eq
      p (fun C => (law_pos H θ ξ C).ne') record y₀ event
      ((embeddedConfigurationRestriction G H f hGH) ⁻¹' B) hEEq
    have hcond' := hcond
    simpa [p, event] using
      (calc
        ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
          p (fun C => (law_pos H θ ξ C).ne') record y₀).toMeasure event).toReal =
            ((PottsContinuity.FKC.FiniteFK.finiteStatisticConditionalPMF
              p (fun C => (law_pos H θ ξ C).ne') record y₀).toMeasure
              ((embeddedConfigurationRestriction G H f hGH) ⁻¹' B)).toReal := hconditionalEq
        _ ≤ ((law H θ (BoundaryCondition.free ξ.boundary)).toMeasure
              ((embeddedConfigurationRestriction G H f hGH) ⁻¹' B)).toReal := hcond'
        _ = (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A :=
              hfreeProbability)
  have hfinite :=
    pmf_event_le_reference_add_bad_of_goodFiberBound
      p hp record good event
      ((boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A)
      hgoodStable (ENNReal.toReal_nonneg) hfreeReference hconditional
  have hAbox :
      (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real A =
        (p.toMeasure event).toReal := by
    have h := boxMeasure_apply θ 1 (0, 0) N hA.measurableSet
    change ((boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration) A).toReal = _
    rw [h]
    simp [p, H, ξ, ext, event, PottsContinuity.PD.FK.measure,
      PottsContinuity.PD.RCInfinite.boxBoundary]
  have herrorBox :
      (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real
          (disconnectionBarrier k M)ᶜ =
        (p.toMeasure (ext ⁻¹' (disconnectionBarrier k M)ᶜ)).toReal := by
    have hErrMeas : MeasurableSet (disconnectionBarrier k M)ᶜ :=
      (disconnectionBarrier_measurable k M).compl
    have h := boxMeasure_apply θ 1 (0, 0) N hErrMeas
    change ((boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration)
      (disconnectionBarrier k M)ᶜ).toReal = _
    rw [h]
    simp [p, H, ξ, ext, PottsContinuity.PD.FK.measure,
      PottsContinuity.PD.RCInfinite.boxBoundary]
  have herrorFinite :
      (p.toMeasure goodᶜ).toReal ≤
        (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real
          (disconnectionBarrier k M)ᶜ := by
    rw [herrorBox]
    have hfinite : p.toMeasure (ext ⁻¹' (disconnectionBarrier k M)ᶜ) ≠ ⊤ :=
      measure_ne_top _ _
    exact MeasureTheory.measureReal_mono hbadSubset hfinite
  calc
    (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real A =
        (p.toMeasure event).toReal := hAbox
    _ ≤ (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A +
        (p.toMeasure goodᶜ).toReal := hfinite
    _ ≤ (boxMeasure θ 0 (0, 0) N : Measure LatticeConfiguration).real A +
        (boxMeasure θ 1 (0, 0) N : Measure LatticeConfiguration).real
          (disconnectionBarrier k M)ᶜ := add_le_add le_rfl herrorFinite
    _ = _ := by rfl

/-- Increasing the outer box can only make disconnection from its boundary
more likely. -/
theorem disconnectionBarrier_mono (k : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    disconnectionBarrier k M ⊆ disconnectionBarrier k N := by
  intro ω hω
  rcases hω with ⟨hkM, hω⟩
  refine ⟨hkM.trans hMN, ?_⟩
  intro x hxk hxN y hy hreach
  by_cases hMN' : M = N
  · subst N
    exact hω x hxk hxN y hy hreach
  have hMNlt : M < N := Nat.lt_of_le_of_ne hMN hMN'
  have hxM : x ∈ latticeBox (0, 0) M :=
    latticeBox_mono (0, 0) hkM hxk
  have hyout : y.val ∉ latticeBox (0, 0) M := by
    intro hyM
    have hcoord := box_boundary_coordinate_edge N hy
    rw [mem_latticeBox] at hyM
    rcases hcoord with hleft | hright | hbottom | htop <;> omega
  obtain ⟨w⟩ := hreach
  let f := boxOpenGraph_hom_global ω N
  have hstart : f ⟨x, hxN⟩ = x := rfl
  have hend : f y = y.val := rfl
  have wg : (rcInfiniteOpenGraph ω).Walk x y.val := by
    rw [← hstart, ← hend]
    exact w.map f
  obtain ⟨z, hzM, p, hpM, y', hzy', hy'⟩ :=
    walk_prefix_to_boundary wg hxM hyout
  have hzBoundary : z ∈ PottsContinuity.PD.vertexBoundary
      (latticeBox (0, 0) M) := by
    refine ⟨hzM, y', ?_, hy'⟩
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω z y').mp hzy'
    exact squareLattice.mem_edgeSet.mp he
  have hpath := p.induce (latticeBox (0, 0) M : Set LatticeVertex) hpM
  have hreachM : (boxOpenGraph ω M).Reachable
      ⟨x, hxM⟩ ⟨z, hzM⟩ := hpath.reachable
  exact hω x hxk hxM ⟨z, hzM⟩ hzBoundary hreachM

/-- If every open cluster is finite, a fixed finite inner box eventually has
no connection to the boundary of the growing induced box. -/
theorem disconnectionBarrier_exhausts_of_allFiniteClusters (k : ℕ)
    (ω : LatticeConfiguration)
    (hfinite : ∀ x : LatticeVertex,
      {y | (rcInfiniteOpenGraph ω).Reachable x y}.Finite) :
    ∃ M, ω ∈ disconnectionBarrier k M := by
  let W : Set LatticeVertex :=
    ⋃ x ∈ (latticeBox (0, 0) k : Set LatticeVertex),
      {y | (rcInfiniteOpenGraph ω).Reachable x y}
  have hW : W.Finite := by
    apply (latticeBox (0, 0) k).finite_toSet.biUnion
    intro x hx
    exact hfinite x
  obtain ⟨R, hR⟩ := finite_vertex_set_subset_box hW
  let M := max k R + 1
  have hMR : R < M := by dsimp [M]; omega
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    omega
  · intro x hxk hxM y hy hreach
    obtain ⟨w⟩ := hreach
    let f := boxOpenGraph_hom_global ω M
    have hstart : f ⟨x, hxM⟩ = x := rfl
    have hend : f y = y.val := rfl
    have hglobal : (rcInfiniteOpenGraph ω).Walk x y.val := by
      rw [← hstart, ← hend]
      exact w.map f
    have hyNotR : y.val ∉ latticeBox (0, 0) R := by
      intro hyR
      have hcoord := box_boundary_coordinate_edge M hy
      rw [mem_latticeBox] at hyR
      rcases hcoord with hleft | hright | hbottom | htop <;> omega
    have hyW : y.val ∈ W := by
      refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxk, ?_⟩⟩
      exact hglobal.reachable
    exact hyNotR (hR hyW)

private theorem disconnectionDMP_from_finiteBoxes
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit p q 1 μ₁)
    (k M : ℕ) (hkM : k ≤ M)
    {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges (0, 0) k) A) (hupper : IsUpperSet A) :
    μ₁.real A ≤ μ₀.real A + μ₁.real (disconnectionBarrier k M)ᶜ := by
  cases Foundations.squareLattice_eq_PD
  let θ := PottsContinuity.Infinite.pdParameters p q hp0 hp1 hq
  let E := (disconnectionBarrier k M)ᶜ
  have hE : IsCylinder E := (disconnectionBarrier_isCylinder k M).compl
  have hEdep : DependsOn (boxEdges (0, 0) M) E :=
    (disconnectionBarrier_dependsOn k M).compl
  have hθP : θ.toP = p := by
    change (PottsContinuity.Infinite.pdParameters p q hp0 hp1 hq).toP = p
    exact PottsContinuity.Infinite.pdParameters_toP p q hp0 hp1 hq
  have hθQ : θ.toQ = q := by
    change (PottsContinuity.Infinite.pdParameters p q hp0 hp1 hq).toQ = q
    exact PottsContinuity.Infinite.pdParameters_toQ p q hp0 hp1 hq
  have hμ₀PD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ₀ := by
    rw [hθP, hθQ]
    exact PottsContinuity.Infinite.isRCInfiniteVolumeLimit_to_PD_box
      p q 0 μ₀ hμ₀
  have hμ₁PD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ₁ := by
    rw [hθP, hθQ]
    exact PottsContinuity.Infinite.isRCInfiniteVolumeLimit_to_PD_box
      p q 1 μ₁ hμ₁
  have hwired := tendsto_cylinder_probability θ 1 μ₁ hμ₁PD hA
  have hfree := tendsto_cylinder_probability θ 0 μ₀ hμ₀PD hA
  have herr := tendsto_cylinder_probability θ 1 μ₁ hμ₁PD hE
  apply le_of_tendsto_of_tendsto hwired (hfree.add herr)
  filter_upwards [eventually_ge_atTop (M + 1)] with N hN
  have hMN : M < N := by omega
  exact disconnection_wiredBox_comparison θ k M N hkM hMN hA hdep hupper

/-- P1 implies equality of the free and wired limits once the finite wired
box comparison is proved for the disconnection barrier. The barrier's
measurability, monotonicity, and exhaustion are discharged here. -/
theorem p1_implies_p2_of_disconnectionDMP
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit p q 1 μ₁)
    (hP1 : μ₁ {ω | {x | (rcInfiniteOpenGraph ω).Reachable (0, 0) x}.Infinite} = 0)
    (hDMP : ∀ k M, k ≤ M →
      ∀ {A : Set LatticeConfiguration}, IsCylinder A →
        DependsOn (boxEdges (0, 0) k) A → IsUpperSet A →
          μ₁.real A ≤ μ₀.real A + μ₁.real (disconnectionBarrier k M)ᶜ) :
    μ₀ = μ₁ := by
  apply p1_implies_p2_of_outermostCircuitDMP p q hp0 hp1 hq μ₀ μ₁ hμ₀ hμ₁ hP1
    disconnectionBarrier
    disconnectionBarrier_measurable
    (fun k M N hMN => disconnectionBarrier_mono k hMN)
    (fun k ω hfinite => disconnectionBarrier_exhausts_of_allFiniteClusters k ω hfinite)
    hDMP

/-- The exact P1⇒P2 link: absence of infinite wired clusters forces equality
of the free and wired infinite-volume limits. The proof uses the disconnection
barrier and its stopped-record free-interior comparison. -/
theorem p1_implies_p2
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit p q 1 μ₁)
    (hP1 : μ₁ {ω | {x | (rcInfiniteOpenGraph ω).Reachable (0, 0) x}.Infinite} = 0) :
    μ₀ = μ₁ := by
  apply p1_implies_p2_of_disconnectionDMP p q hp0 hp1 hq μ₀ μ₁ hμ₀ hμ₁ hP1
  intro k M hkM A hA hdep hupper
  exact disconnectionDMP_from_finiteBoxes p q hp0 hp1 hq μ₀ μ₁
    hμ₀ hμ₁ k M hkM hA hdep hupper
end

end PottsContinuity.Thm3.Easy
