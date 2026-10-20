module

public import PottsContinuity.Thm4Records.ActualSourceRecords

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane PlanarMixed.Lemma4Connectors
noncomputable section

/-- Passing to incident vertices preserves each original sampled open step. -/
theorem openGraph_incidentRead_adj {V : Type*} [Finite V]
    (G : SimpleGraph V) (C : Configuration G)
    (u v : incidentVertexSet G) (huv : (openGraph G C).Adj u.val v.val) :
    (openGraph (G.induce (incidentVertexSet G)) (incidentVertexConfigurationRead G C)).Adj u v := by
  obtain ⟨e,he,heq⟩ := (openGraph_adj G C _ _).mp huv
  let d : (G.induce (incidentVertexSet G)).edgeSet :=
    ⟨s(u,v),(G.induce (incidentVertexSet G)).mem_edgeSet.mpr (openGraph_le G C huv)⟩
  apply (openGraph_adj _ _ _ _).mpr
  refine ⟨d,?_,rfl⟩
  apply (mem_embeddedConfigurationRestriction _ _ _ _ C d).mpr
  have hed : embeddedEdgeEmbedding _ G (incidentVertexEmbedding G)
      (incidentVertexGraph_map G).le d=e := by
    apply Subtype.ext
    exact heq.symm
  rw [hed]
  exact he

/-- A genuine sampled path lifts without deleting or restoring any bond. -/
theorem openGraph_incidentRead_walk {V : Type*} [Finite V]
    (G : SimpleGraph V) (C : Configuration G) {u v : V}
    (p : (openGraph G C).Walk u v)
    (hu : u ∈ incidentVertexSet G) (hv : v ∈ incidentVertexSet G) :
    Nonempty ((openGraph (G.induce (incidentVertexSet G))
      (incidentVertexConfigurationRead G C)).Walk ⟨u,hu⟩ ⟨v,hv⟩) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons u w v huw p ih =>
    have hw : w ∈ incidentVertexSet G := ⟨u,(openGraph_le G C huw).symm⟩
    obtain ⟨q⟩ := ih hw hv
    exact ⟨.cons (openGraph_incidentRead_adj G C ⟨u,hu⟩ ⟨w,hw⟩ huw) q⟩

/-- Nontrivial connectivity on the original carrier lies entirely on incident
vertices; isolated vertices cannot create a connection. -/
theorem actualConnected_incidentRead_of_ne {V : Type*} [Finite V]
    (G : SimpleGraph V) (C : Configuration G) {u v : V}
    (hne : u ≠ v) (hconn : ActualConnected G C u v) :
    ∃ hu : u ∈ incidentVertexSet G, ∃ hv : v ∈ incidentVertexSet G,
      ActualConnected (G.induce (incidentVertexSet G)) (incidentVertexConfigurationRead G C)
        ⟨u,hu⟩ ⟨v,hv⟩ := by
  obtain ⟨w,huw⟩ := hconn.nonempty_neighborSet_left hne
  obtain ⟨z,hvz⟩ := hconn.nonempty_neighborSet_right hne
  have hu : u ∈ incidentVertexSet G := ⟨w,openGraph_le G C huw⟩
  have hv : v ∈ incidentVertexSet G := ⟨z,openGraph_le G C hvz⟩
  obtain ⟨p⟩ := hconn
  exact ⟨hu,hv,openGraph_incidentRead_walk G C p hu hv⟩

/-- Native bottom seeds retain their literal original source labels. -/
def connectorBottomCluster (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X)) :
    Set (FKC.FiniteFK.SlitBoxVertex (16*m)) :=
  {v | ∃ s : FKC.FiniteFK.SlitBoxVertex (16*m), s.val.2=-(12*(m:ℤ)) ∧
    ActualConnected (connectorNativeGraph m hm X)
      ((edgeRestrictionConfigurationEquiv _ (connectorReveal m hm X)).symm U) s v}

/-- Every native bottom seed is reached, even if it is an isolated vertex. -/
theorem connectorBottomCluster_contains_bottom (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (s : FKC.FiniteFK.SlitBoxVertex (16*m)) (hs : s.val.2=-(12*(m:ℤ))) :
    s ∈ connectorBottomCluster m hm X U := ⟨s,hs,SimpleGraph.Reachable.refl _⟩

/-- The corrected no-crossing event forces the top labels to be unreached. -/
theorem connectorBottomCluster_avoids_top_of_noncrossing (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X)
    (v : FKC.FiniteFK.SlitBoxVertex (16*m)) (hv : v.val.2=-(2*(m:ℤ))) :
    v ∉ connectorBottomCluster m hm X U := by
  rintro ⟨s,hs,hconn⟩
  have hne : s ≠ v := by
    intro h
    have hcoord := congrArg (fun z : FKC.FiniteFK.SlitBoxVertex (16*m) => z.val.2) h
    omega
  obtain ⟨hsi,hvi,hconn'⟩ := actualConnected_incidentRead_of_ne _ _ hne hconn
  exact hnon ⟨⟨s,hsi⟩,⟨v,hvi⟩,hs,hv,hconn'⟩

end
end PottsContinuity.Thm4Records
