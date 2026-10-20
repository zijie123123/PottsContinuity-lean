module

public import PottsContinuity.PlanarMixed.RankedBandPaths
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.Thm3.RSW.FiniteOmegaComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

-- Generalization of the square-specific private separation proof in RankedBand.
/-- Local band edges and labels on two arbitrary wired reference arcs prove
the induced partition bound for EVERY exterior configuration. -/
theorem rankedBand_exterior_partition_le
    {V : Type*} [Finite V] (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) (L R : Set V) (hdis : Disjoint L R)
    (hleft : ∀ v ∈ L, r v ≤ 1) (hright : ∀ v ∈ R, 3 ≤ r v) :
    ∀ K : RemovedConfiguration G
      (subgraphRemovedEdges ((rankedBandGraph G r).map (rankedBandEmbedding r)) G),
      (isolatedExtensionPullbackBoundary (rankedBandEmbedding r)
        (frozenBoundary (twoBlockBoundary L R hdis) K.val)).partition ≤
          (rankedBandBoundary r).partition := by
  have hd : Disjoint {v | r v ≤ 1} {v | 3 ≤ r v} := by
    apply Set.disjoint_left.mpr
    intro v h1 h3
    change r v ≤ 1 at h1
    change 3 ≤ r v at h3
    omega
  let σ := (twoBlockBoundary {v | r v ≤ 1} {v | 3 ≤ r v} hd).partition
  apply RSW.embedded_exterior_partition_le_of_separation
    (rankedBandGraph G r) G (rankedBandEmbedding r)
    (twoBlockBoundary L R hdis) (rankedBandBoundary r) σ
  · intro u v huv
    apply (twoBlockBoundary_partition_rel _ _ hd u v).mpr
    rcases (twoBlockBoundary_partition_rel L R hdis u v).mp huv with h | hL | hR
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hleft u hL.1,hleft v hL.2⟩)
    · exact Or.inr (Or.inr ⟨hright u hR.1,hright v hR.2⟩)
  · intro u v huv
    have hG := openGraph_le G _ huv
    apply (twoBlockBoundary_partition_rel _ _ hd u v).mpr
    rcases hstep u v hG with hL | hband | hR
    · exact Or.inr (Or.inl hL)
    · obtain ⟨e,he,heq⟩ := (openGraph_adj G _ u v).mp huv
      exfalso
      apply (mem_subgraphRemovedEdges e).mp he
      rw [heq]
      apply ((rankedBandGraph G r).map (rankedBandEmbedding r)).mem_edgeSet.mpr
      exact (SimpleGraph.map_adj _ _ _ _).mpr
        ⟨⟨u,hband.1⟩,⟨v,hband.2⟩,hG,rfl,rfl⟩
    · exact Or.inr (Or.inr hR)
  · intro u v huv
    change σ.r u.val v.val at huv
    rcases (twoBlockBoundary_partition_rel _ _ hd u.val v.val).mp huv with h | hL | hR
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inl (Subtype.ext h))
    · change r u.val ≤ 1 ∧ r v.val ≤ 1 at hL
      have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
      have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
      exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inl ⟨by change r u.val = 1; omega,by change r v.val = 1; omega⟩))
    · change 3 ≤ r u.val ∧ 3 ≤ r v.val at hR
      have hu : 1 ≤ r u.val ∧ r u.val ≤ 3 := u.property
      have hv : 1 ≤ r v.val ∧ r v.val ≤ 3 := v.property
      exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr
        (Or.inr (Or.inr ⟨by change r u.val = 3; omega,by change r v.val = 3; omega⟩))

/-- An actual connection of arbitrary reference arcs restricts to an actual
band connection. No additional edges or virtual boundary links are used. -/
theorem rankedBand_arcs_connection_restricts
    {V : Type*} [Finite V] (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) (L R : Set V)
    (hleft : ∀ v ∈ L, r v ≤ 1) (hright : ∀ v ∈ R, 3 ≤ r v)
    (C : Configuration G) (hC : C ∈ arcsConnectionEvent G L R) :
    embeddedConfigurationRestriction (rankedBandGraph G r) G (rankedBandEmbedding r)
      (rankedBandGraph_map_le G r) C ∈
        arcsConnectionEvent (rankedBandGraph G r)
          (rankedBandFirstArc r) (rankedBandSecondArc r) := by
  obtain ⟨u,hu,v,hv,p⟩ := hC
  obtain ⟨p⟩ := p
  have hopen : RankedBandEdges (openGraph G C) r :=
    fun x y h => hstep x y (openGraph_le G C h)
  obtain ⟨x,y,t,_,hx,hy,ht⟩ := rankedBand_subwalk r hopen p (hleft u hu) (hright v hv)
  let f : ((openGraph G C).induce (rankedBandVertices r)) →g
      openGraph (rankedBandGraph G r)
        (embeddedConfigurationRestriction _ G (rankedBandEmbedding r)
          (rankedBandGraph_map_le G r) C) := {
    toFun := id
    map_rel' := fun {u v} h =>
      (embeddedRestriction_openGraph_adj_iff _ G _ (rankedBandGraph_map_le G r) C u v).mpr
        ⟨openGraph_le G C h,h⟩ }
  exact ⟨⟨x,ht x t.start_mem_support⟩,hx,⟨y,ht y t.end_mem_support⟩,hy,
    (t.induce (rankedBandVertices r) ht |>.map f).reachable⟩

end
end PottsContinuity.PlanarMixed
