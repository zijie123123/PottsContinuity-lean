module

public import PottsContinuity.PlanarMixed.BandComparisonGeometry
public import PottsContinuity.PlanarMixed.CanonicalCutCarrier
public import PottsContinuity.PlanarTopology.BoundaryWalkClipping

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 PlanarTopology
noncomputable section

/-- The carrier omitting exactly the internal bonds of the two wired arcs. -/
theorem bandActive_map_le {V : Type*} [Finite V] (G : SimpleGraph V) (r : V → ℤ) :
    (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map (rankedBandEmbedding r) ≤ G :=
  (SimpleGraph.map_monotone _ (edgeRestriction_le _ _)).trans (rankedBandGraph_map_le G r)

/-- Arbitrary reference arcs may be used when they lie on opposite sides
of the same separating band. Every removed-edge state is covered. -/
theorem band_active_reference_partition_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    (L R : Set V) (hLR : Disjoint L R)
    (hL : ∀ v ∈ L, r v ≤ 1) (hR : ∀ v ∈ R, 3 ≤ r v)
    (K : RemovedConfiguration G
      (subgraphRemovedEdges ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map (rankedBandEmbedding r)) G)) :
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
    have hG := openGraph_le G K.val huv
    obtain ⟨e,he,heq⟩ := (openGraph_adj G K.val u v).mp huv
    have heout : e ∈ outerCutReveal G r := by
      rw [outerCutReveal_eq_active_complement G r hstep]
      exact K.property he
    have hepair : (⟨s(u,v),G.mem_edgeSet.mpr hG⟩ : G.edgeSet) = e :=
      Subtype.ext heq.symm
    rw [← hepair] at heout
    rcases (mem_outerCutReveal_pair G r u v hG).mp heout with h | h
    · exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr (Or.inl h))
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
/-- Every sampled reference crossing clips to the active band, without
using any previously exposed internal path bond. -/
theorem band_active_reference_crossing_restricts {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V → ℤ) (hstep : RankedBandEdges G r)
    (L R : Set V) (hL : ∀ v ∈ L, r v ≤ 1) (hR : ∀ v ∈ R, 3 ≤ r v)
    (C : Configuration G) (hC : C ∈ arcsConnectionEvent G L R) :
    embeddedConfigurationRestriction
      (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)) G (rankedBandEmbedding r)
      (bandActive_map_le G r) C ∈
        arcsConnectionEvent _ (rankedBandFirstArc r) (rankedBandSecondArc r) := by
  have hc := band_reference_crossing_restricts G r hstep L R hL hR C hC
  obtain ⟨u,hu,v,hv,⟨p⟩⟩ := hc
  obtain ⟨x,hx,y,hy,t,_,hfirst,hsecond⟩ := walk_subwalk_between_sets p
    (rankedBandFirstArc r) (rankedBandSecondArc r) hu hv
  let f : ((openGraph (rankedBandGraph G r)
      (embeddedConfigurationRestriction _ G (rankedBandEmbedding r)
        (rankedBandGraph_map_le G r) C)).induce {z | z ∈ t.support}) →g
      openGraph (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r))
        (embeddedConfigurationRestriction _ G (rankedBandEmbedding r) (bandActive_map_le G r) C) :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        have hG := openGraph_le (rankedBandGraph G r) _ hab
        have hnot : (⟨s(a.val,b.val),(rankedBandGraph G r).mem_edgeSet.mpr hG⟩ :
            (rankedBandGraph G r).edgeSet) ∉ bandArcBonds G r := by
          intro he
          rcases (mem_bandArcBonds_pair G r a.val b.val hG).mp he with h | h
          · have ha := hfirst a.val a.property h.1
            have hb := hfirst b.val b.property h.2
            exact hG.ne (ha.trans hb.symm)
          · have ha := hsecond a.val a.property h.1
            have hb := hsecond b.val b.property h.2
            exact hG.ne (ha.trans hb.symm)
        apply (embeddedRestriction_openGraph_adj_iff _ G (rankedBandEmbedding r)
          (bandActive_map_le G r) C a.val b.val).mpr
        constructor
        · apply (SimpleGraph.deleteEdges_adj (G := rankedBandGraph G r)).mpr
          exact ⟨hG,fun he => hnot ((coe_mem_openEdges_iff _ _ _).mp he)⟩
        · exact ((embeddedRestriction_openGraph_adj_iff _ G (rankedBandEmbedding r)
            (rankedBandGraph_map_le G r) C a.val b.val).mp hab).2 }
  exact ⟨x,hx,y,hy,(t.induce {z | z ∈ t.support} (fun _ hz => hz) |>.map f).reachable⟩

end
end PottsContinuity.PlanarMixed
