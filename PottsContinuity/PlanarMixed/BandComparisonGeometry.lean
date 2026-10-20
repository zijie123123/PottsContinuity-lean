module

public import PottsContinuity.PlanarMixed.RankedBandPaths
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Arbitrary reference arcs may be used when they lie on opposite sides
of the same separating band. Every removed-edge state is covered. -/
theorem band_reference_partition_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    (L R : Set V) (hLR : Disjoint L R)
    (hL : ∀ v ∈ L, r v ≤ 1) (hR : ∀ v ∈ R, 3 ≤ r v)
    (K : RemovedConfiguration G
      (subgraphRemovedEdges ((rankedBandGraph G r).map (rankedBandEmbedding r)) G)) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding r)
      (frozenBoundary (twoBlockBoundary L R hLR) K.val)).partition ≤
      (rankedBandBoundary r).partition := by
  have hsep : Disjoint {v | r v ≤ 1} {v | 3 ≤ r v} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    change r v ≤ 1 at hv
    change 3 ≤ r v at hw
    omega
  let σ := (twoBlockBoundary {v | r v ≤ 1} {v | 3 ≤ r v} hsep).partition
  have href : (twoBlockBoundary L R hLR).partition ≤ σ := by
    intro u v huv
    rcases (twoBlockBoundary_partition_rel _ _ _ u v).mp huv with h | h | h
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl h)
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inl ⟨hL u h.1, hL v h.2⟩))
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inr ⟨hR u h.1, hR v h.2⟩))
  have hedge : ∀ ⦃u v⦄, (openGraph G K.val).Adj u v → σ.r u v := by
    intro u v huv
    rcases hstep u v (openGraph_le G K.val huv) with h | h | h
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inl h))
    · obtain ⟨e, he, heq⟩ := (openGraph_adj G K.val u v).mp huv
      have hn := (mem_subgraphRemovedEdges e).mp (K.property he)
      apply False.elim
      apply hn
      rw [heq]
      apply ((rankedBandGraph G r).map (rankedBandEmbedding r)).mem_edgeSet.mpr
      exact (SimpleGraph.map_adj _ _ _ _).mpr
        ⟨⟨u,h.1⟩,⟨v,h.2⟩,openGraph_le G K.val huv,rfl,rfl⟩
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inr h))
  have hcomp : componentSetoid G (twoBlockBoundary L R hLR) K.val ≤ σ := by
    apply componentSetoid_le
    · intro u v hconn
      obtain ⟨p⟩ := (actualConnected_iff_walk _ _ u v).mp hconn
      induction p with
      | nil => exact σ.refl _
      | @cons u v w huv p ih => exact σ.trans (hedge huv) (ih p.reachable)
    · exact href
  intro u v huv
  have h := hcomp huv
  rcases (twoBlockBoundary_partition_rel _ _ _ u.val v.val).mp h with h | h | h
  · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl (Subtype.ext h))
  · change r u.val ≤ 1 ∧ r v.val ≤ 1 at h
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inl ⟨by change r u.val = 1; omega, by change r v.val = 1; omega⟩))
  · change 3 ≤ r u.val ∧ 3 ≤ r v.val at h
    have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
    have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
    exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
      (Or.inr (Or.inr ⟨by change r u.val = 3; omega, by change r v.val = 3; omega⟩))

theorem band_restriction_open_adj {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (C : Configuration G)
    (u v : rankedBandVertices r) (h : (openGraph G C).Adj u.val v.val) :
    (openGraph (rankedBandGraph G r)
      (embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
        (rankedBandGraph_map_le G r) C)).Adj u v := by
  let e : (rankedBandGraph G r).edgeSet :=
    ⟨s(u,v), (rankedBandGraph G r).mem_edgeSet.mpr (openGraph_le G C h)⟩
  obtain ⟨a, ha, haq⟩ := (openGraph_adj G C u.val v.val).mp h
  have he : embeddedEdgeEmbedding _ _ (rankedBandEmbedding r)
      (rankedBandGraph_map_le G r) e = a := by
    apply Subtype.ext
    change Sym2.map Subtype.val s(u,v) = a.val
    exact haq.symm
  apply (openGraph_adj _ _ u v).mpr
  refine ⟨e, ?_, rfl⟩
  change e ∈ embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
    (rankedBandGraph_map_le G r) C
  rw [mem_embeddedConfigurationRestriction, he]
  exact ha

/-- Clipping is independent of the ambient rectangle's orientation. -/
theorem band_reference_crossing_restricts {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    (L R : Set V) (hL : ∀ v ∈ L, r v ≤ 1) (hR : ∀ v ∈ R, 3 ≤ r v)
    (C : Configuration G) (hC : C ∈ arcsConnectionEvent G L R) :
    embeddedConfigurationRestriction (rankedBandGraph G r) G (rankedBandEmbedding r)
      (rankedBandGraph_map_le G r) C ∈
        arcsConnectionEvent _ (rankedBandFirstArc r) (rankedBandSecondArc r) := by
  obtain ⟨u,hu,v,hv,hp⟩ := hC
  obtain ⟨p⟩ := (actualConnected_iff_walk _ _ u v).mp hp
  have hopen : RankedBandEdges (openGraph G C) r :=
    fun x y h => hstep x y (openGraph_le G C h)
  obtain ⟨x,y,t,_,hx,hy,ht⟩ := rankedBand_subwalk r hopen p (hL u hu) (hR v hv)
  let tx : rankedBandVertices r := ⟨x,ht x t.start_mem_support⟩
  let ty : rankedBandVertices r := ⟨y,ht y t.end_mem_support⟩
  let f : ((openGraph G C).induce (rankedBandVertices r)) →g
      openGraph (rankedBandGraph G r)
        (embeddedConfigurationRestriction _ _ (rankedBandEmbedding r)
          (rankedBandGraph_map_le G r) C) :=
    { toFun := id
      map_rel' := fun {u v} h => band_restriction_open_adj G r C u v h }
  exact ⟨tx,hx,ty,hy,(t.induce (rankedBandVertices r) ht |>.map f).reachable⟩

end
end PottsContinuity.PlanarMixed
