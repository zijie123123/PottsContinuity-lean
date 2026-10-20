module

public import PottsContinuity.Thm4Plane.ScreenTargetCap
public import PottsContinuity.Exploration.BoundaryClusterStatisticDMP

@[expose] public section

namespace PottsContinuity.Thm4Plane

noncomputable section

open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK

local instance screenBoundaryClusterFiberEdgeFintype {V : Type*}
    {G : SimpleGraph V} [Finite V] : Fintype G.edgeSet := Fintype.ofFinite _
local instance screenBoundaryClusterFiberEdgeDecidableEq {V : Type*}
    {G : SimpleGraph V} [Finite V] : DecidableEq G.edgeSet := Classical.decEq _

private theorem screenOpenAdj_iff_bond_mem
    {V : Type*} {G : SimpleGraph V} [Finite V]
    (C : Configuration G) {x y : V} (hxy : G.Adj x y) :
    (openGraph G C).Adj x y ↔
      (⟨s(x, y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∈ C := by
  rw [openGraph_adj]
  change s(x, y) ∈ Subtype.val '' (↑C : Set G.edgeSet) ↔ _
  constructor
  · rintro ⟨e, he, heval⟩
    have heq : e = ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩ := Subtype.ext heval
    simpa [heq] using he
  · intro he
    exact ⟨⟨s(x, y), G.mem_edgeSet.mpr hxy⟩, he, rfl⟩

private theorem screenBoundaryTouchCluster_subset_of_record_agreement
    {V : Type*} {G : SimpleGraph V} [Finite V]
    (S : Set V) (C C' : Configuration G)
    (hagree : ∀ e ∈ boundaryClusterRevealEdges S C,
      (e ∈ C ↔ e ∈ C')) :
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
      have hx : x ∈ boundaryTouchCluster S C := ⟨b, hb, hprev⟩
      have hxyG : G.Adj x y := (openGraph_le G C) hxy
      have hxy' : (openGraph G C').Adj x y := by
        apply (screenOpenAdj_iff_bond_mem C' hxyG).2
        exact (hagree ⟨s(x, y), G.mem_edgeSet.mpr hxyG⟩
          (boundaryCluster_edge_mem_reveal S C hx hxyG)).1
          ((screenOpenAdj_iff_bond_mem C hxyG).1 hxy)
      exact Relation.ReflTransGen.tail ih' hxy'

private theorem screenBoundaryTouchCluster_reverse_of_record_agreement
    {V : Type*} {G : SimpleGraph V} [Finite V]
    (S : Set V) (C C' : Configuration G)
    (hagree : ∀ e ∈ boundaryClusterRevealEdges S C,
      (e ∈ C ↔ e ∈ C')) :
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
      have hx : x ∈ boundaryTouchCluster S C :=
        ⟨b, hb, (SimpleGraph.reachable_iff_reflTransGen b x).2 ih'⟩
      have hxyG : G.Adj x y := (openGraph_le G C') hxy
      have hxyC : (openGraph G C).Adj x y := by
        apply (screenOpenAdj_iff_bond_mem C hxyG).2
        exact (hagree ⟨s(x, y), G.mem_edgeSet.mpr hxyG⟩
          (boundaryCluster_edge_mem_reveal S C hx hxyG)).2
          ((screenOpenAdj_iff_bond_mem C' hxyG).1 hxy)
      exact Relation.ReflTransGen.tail ih' hxyC

/-- Agreement of boundary-cluster records forces the same unreached vertex set. -/
theorem boundaryClusterInterior_eq_of_boundaryClusterStatistic_eq
    {V : Type*} {G : SimpleGraph V} [Finite V]
    (S : Set V) (C C' : Configuration G)
    (hrecord : boundaryClusterStatistic S C' = boundaryClusterStatistic S C) :
    boundaryClusterInterior S C' = boundaryClusterInterior S C := by
  have hstates :
      C' ∩ boundaryClusterRevealMap S C =
        C ∩ boundaryClusterRevealMap S C := by
    have hsnd := congrArg Prod.snd hrecord
    change C' ∩ boundaryClusterRevealMap S C' =
      C ∩ boundaryClusterRevealMap S C at hsnd
    have hfst := congrArg Prod.fst hrecord
    change boundaryClusterRevealMap S C' = boundaryClusterRevealMap S C at hfst
    rw [hfst] at hsnd
    exact hsnd
  have hagree : ∀ e ∈ boundaryClusterRevealEdges S C,
      (e ∈ C ↔ e ∈ C') := by
    intro e he
    constructor
    · intro hc
      have hmem : e ∈ C ∩ boundaryClusterRevealMap S C :=
        Finset.mem_inter.mpr ⟨hc, he⟩
      rw [← hstates] at hmem
      exact (Finset.mem_inter.mp hmem).1
    · intro hc'
      have hmem : e ∈ C' ∩ boundaryClusterRevealMap S C :=
        Finset.mem_inter.mpr ⟨hc', he⟩
      rw [hstates] at hmem
      exact (Finset.mem_inter.mp hmem).1
  have hcluster : boundaryTouchCluster S C' = boundaryTouchCluster S C :=
    Set.Subset.antisymm
      (screenBoundaryTouchCluster_reverse_of_record_agreement S C C' hagree)
      (screenBoundaryTouchCluster_subset_of_record_agreement S C C' hagree)
  change (boundaryTouchCluster S C')ᶜ = (boundaryTouchCluster S C)ᶜ
  rw [hcluster]

/-- The cap-containment event is measurable from the boundary-cluster record. -/
def screenBoundaryClusterGood (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) : Prop :=
  screenTargetCap m ⊆ boundaryClusterInterior
    (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) A

theorem screenBoundaryClusterGood_stable_on_statistic_fiber
    (m : ℕ) (A B : Configuration (slitBoxGraph (16 * m)))
    (hrecord : boundaryClusterStatistic
      (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) B =
      boundaryClusterStatistic
      (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) A) :
    (screenBoundaryClusterGood m A ↔ screenBoundaryClusterGood m B) := by
  unfold screenBoundaryClusterGood
  rw [boundaryClusterInterior_eq_of_boundaryClusterStatistic_eq
    (slitBoxWiredArc (16 * m) : Set (SlitBoxVertex (16 * m))) A B hrecord]

end

end PottsContinuity.Thm4Plane
