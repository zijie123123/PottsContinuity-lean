module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.Exploration.FrozenBoundaryFreeInterior
public import PottsContinuity.Exploration.InteriorFreeLaw
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! A finite wired-boundary cluster exploration and its conditional law. -/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable section

local instance boundaryClusterEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundaryClusterEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
/-- Vertices connected by actual open edges to a selected boundary seed set. -/
def boundaryTouchCluster (S : Set V) (C : Configuration G) : Set V :=
  {v | ∃ b, b ∈ S ∧ ActualConnected G C b v}

/-- The vertices not reached by the open cluster from the seed set. -/
def boundaryClusterInterior (S : Set V) (C : Configuration G) : Set V :=
  (boundaryTouchCluster S C)ᶜ

omit [Finite V] in

omit [Finite V] in

omit [Finite V] in

omit [Finite V] in

abbrev boundaryClusterEmbedding (S : Set V) (C : Configuration G) :
    {v // v ∈ boundaryClusterInterior S C} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

local instance boundaryClusterInteriorEdgeFintype {S : Set V} (C : Configuration G) :
    Fintype ((SimpleGraph.map (boundaryClusterEmbedding S C)
      (SimpleGraph.induce (boundaryClusterInterior S C) G)).edgeSet) :=
  Fintype.ofFinite _
local instance boundaryClusterInteriorEdgeDecidableEq {S : Set V} (C : Configuration G) :
    DecidableEq ((SimpleGraph.map (boundaryClusterEmbedding S C)
      (SimpleGraph.induce (boundaryClusterInterior S C) G)).edgeSet) :=
  Classical.decEq _

/-- The edges left after the complete exterior of that interior is exposed. -/
def boundaryClusterRevealEdges (S : Set V) (C : Configuration G) : Configuration G :=
  subgraphRemovedEdges
    (SimpleGraph.map (boundaryClusterEmbedding S C)
      (SimpleGraph.induce (boundaryClusterInterior S C) G)) G

/-- Record the states of every edge not internal to the unreached region. -/
def boundaryClusterRevealMap (S : Set V) : RevealMap (G := G) :=
  fun C => boundaryClusterRevealEdges S C

omit [Finite V] in
private theorem boundaryTouchCluster_open_adj_closed (S : Set V)
    (C : Configuration G) {x y : V}
    (hx : x ∈ boundaryTouchCluster S C)
    (hxy : (openGraph G C).Adj x y) : y ∈ boundaryTouchCluster S C := by
  rcases hx with ⟨b, hb, hbx⟩
  exact ⟨b, hb, hbx.trans hxy.reachable⟩

private theorem boundaryCluster_edge_not_reveal_of_both_interior
    (S : Set V) (C : Configuration G) {x y : V}
    (hx : x ∈ boundaryClusterInterior S C) (hy : y ∈ boundaryClusterInterior S C)
    (hxy : G.Adj x y) :
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

theorem boundaryCluster_edge_mem_reveal (S : Set V) (C : Configuration G)
    {x y : V} (hx : x ∈ boundaryTouchCluster S C) (hxy : G.Adj x y) :
    (⟨s(x,y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∈ boundaryClusterRevealEdges S C := by
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

omit [Finite V] in
private theorem openGraph_adj_iff_edge_mem (C : Configuration G)
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

private theorem openGraph_adj_iff_of_boundaryCluster_agreement (S : Set V)
    (C C' : Configuration G)
    (hagree : ∀ e ∈ boundaryClusterRevealEdges S C, (e ∈ C ↔ e ∈ C'))
    {x y : V} (hx : x ∈ boundaryTouchCluster S C) (hxy : G.Adj x y) :
    ((openGraph G C).Adj x y ↔ (openGraph G C').Adj x y) := by
  rw [openGraph_adj_iff_edge_mem C hxy, openGraph_adj_iff_edge_mem C' hxy]
  exact hagree ⟨s(x,y), G.mem_edgeSet.mpr hxy⟩
    (boundaryCluster_edge_mem_reveal S C hx hxy)

private theorem boundaryTouchCluster_subset_of_reveal_agreement (S : Set V)
    (C C' : Configuration G)
    (hagree : ∀ e ∈ boundaryClusterRevealEdges S C, (e ∈ C ↔ e ∈ C')) :
    boundaryTouchCluster S C ⊆ boundaryTouchCluster S C' := by
  intro v hv
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
      have hx : x ∈ boundaryTouchCluster S C := ⟨b, hb,
        hprev⟩
      exact Relation.ReflTransGen.tail ih'
        ((openGraph_adj_iff_of_boundaryCluster_agreement S C C' hagree hx
          ((openGraph_le G C) hxy)).mp hxy)

private theorem boundaryTouchCluster_reverse_of_reveal_agreement (S : Set V)
    (C C' : Configuration G)
    (hagree : ∀ e ∈ boundaryClusterRevealEdges S C, (e ∈ C ↔ e ∈ C')) :
    boundaryTouchCluster S C' ⊆ boundaryTouchCluster S C := by
  intro v hv
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
      have hx : x ∈ boundaryTouchCluster S C := ⟨b, hb,
        (SimpleGraph.reachable_iff_reflTransGen b x).2 ih'⟩
      have hxyG : G.Adj x y := (openGraph_le G C') hxy
      have hopenC : (openGraph G C).Adj x y := by
        by_contra hclosed
        have he := (openGraph_adj_iff_edge_mem C' hxyG).mp hxy
        have he' : (⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩ : G.edgeSet) ∈ C :=
          (hagree ⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩
            (boundaryCluster_edge_mem_reveal S C hx hxyG)).mpr he
        exact hclosed ((openGraph_adj_iff_edge_mem C hxyG).mpr he')
      exact Relation.ReflTransGen.tail ih' hopenC

/-- The unreached region and its exterior edge set are stable under agreement
on the recorded exterior states. -/
theorem boundaryClusterRevealMap_stable (S : Set V) :
    ∀ (C C' : Configuration G),
      C' ∩ boundaryClusterRevealMap S C = C ∩ boundaryClusterRevealMap S C →
      boundaryClusterRevealMap S C' = boundaryClusterRevealMap S C := by
  intro C C' hrecord
  have hagree : ∀ e ∈ boundaryClusterRevealEdges S C, (e ∈ C ↔ e ∈ C') := by
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
    Set.Subset.antisymm
      (boundaryTouchCluster_reverse_of_reveal_agreement S C C' hagree)
      (boundaryTouchCluster_subset_of_reveal_agreement S C C' hagree)
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

theorem boundaryCluster_revealed_open_no_incident (S : Set V)
    (C : Configuration G) {x y : V} (hx : x ∈ boundaryClusterInterior S C)
    (hxy : (openGraph G (revealRecordConfiguration (boundaryClusterRevealMap S) C).val).Adj x y) :
    False := by
  have hxyG : G.Adj x y := (openGraph_le G _) hxy
  have he := (openGraph_adj_iff_edge_mem _ hxyG).mp hxy
  have hstate :
      (⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩ : G.edgeSet) ∈
        (C ∩ boundaryClusterRevealEdges S C) := by
    simpa [revealRecordConfiguration, boundaryClusterRevealMap] using he
  have hstate' := Finset.mem_inter.mp hstate
  have horiginal :
      (⟨s(x,y), G.mem_edgeSet.mpr hxyG⟩ : G.edgeSet) ∈ C := hstate'.1
  have hycluster : y ∈ boundaryTouchCluster S C := by
    by_contra hy
    exact boundaryCluster_edge_not_reveal_of_both_interior S C hx
      (by simpa [boundaryClusterInterior] using hy) hxyG hstate'.2
  have hopenC : (openGraph G C).Adj x y :=
    (openGraph_adj_iff_edge_mem C hxyG).mpr horiginal
  exact hx (boundaryTouchCluster_open_adj_closed S C hycluster hopenC.symm)

end
end PottsContinuity.Exploration
