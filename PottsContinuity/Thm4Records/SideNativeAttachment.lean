module

public import PottsContinuity.Thm4Records.NativeCoordinates
public import PottsContinuity.Thm4Records.CensoredOpenAttachment
public import PottsContinuity.Thm4Records.Selection

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- Every reached side-cluster vertex belongs to the censored side window. -/
theorem sideOuterCluster_subset_sideWindow (m : ℕ) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Thm3.Prop4.censoredSeedCluster (sideCensoredGraph_le m right) (sideOuterSeeds m right) X ⊆
      sideWindow m right := by
  rintro u ⟨s,hs,hsu⟩
  by_cases h : s=u
  · subst u
    cases right <;> dsimp [sideOuterSeeds,sideWindow] at hs ⊢ <;> omega
  · obtain ⟨v,hv⟩ := hsu.nonempty_neighborSet_right h
    exact (openGraph_le _ _ hv).2.1

private theorem source_edge_eq_pair_of_endpoints (m : ℕ)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (u v : FKC.FiniteFK.SlitBoxVertex (16*m))
    (hu : u ∈ e.val) (hv : v ∈ e.val) (hne : u ≠ v) : e.val = s(u,v) := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  change s(a,b)=e.val at hab
  rw [← hab] at hu hv ⊢
  rcases Sym2.mem_iff'.mp hu with rfl | rfl <;>
    rcases Sym2.mem_iff'.mp hv with rfl | rfl
  · exact False.elim (hne rfl)
  · rfl
  · exact Sym2.eq_swap
  · exact False.elim (hne rfl)

/-- On failure of the opposite-side primal connection, an open side-query
bond cannot attach to any vertex carrying an unrevealed original bond. -/
theorem sideOpenQuery_no_native_attachment_of_no_primal_connection
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (he : e ∈ X) (hr : e ∈ sideOuterClusterReveal m right X)
    (u : connectorNativeVertex m hm X) : u.val ∉ e.val := by
  intro hue
  obtain ⟨v,hv,hvc⟩ := (Thm3.Prop4.mem_censoredSeedReveal _ _ X e).mp hr
  obtain ⟨w,huw⟩ := u.property
  obtain ⟨hG,hd⟩ := (PlanarMixed.edgeRestriction_adj_exists_not_mem _ _ u.val w).mp huw
  have huc : u.val ∉ Thm3.Prop4.censoredSeedCluster
      (sideCensoredGraph_le m right) (sideOuterSeeds m right) X := by
    intro hc
    apply hd
    apply sideOuterClusterReveal_subset_connectorReveal m hm right X
    exact (Thm3.Prop4.mem_censoredSeedReveal _ _ X _).mpr
      ⟨u.val,Sym2.mem_mk_left _ _,hc⟩
  have huv : u.val ≠ v := by intro h; exact huc (h ▸ hvc)
  have hpair := source_edge_eq_pair_of_endpoints m e u.val v hue hv huv
  have hadj : (FKC.FiniteFK.slitBoxGraph (16*m)).Adj u.val v := by
    apply (FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mp
    rw [← hpair]
    exact e.property
  have hstep := (FKC.squareLattice_adj_iff _ _).mp
    ((FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mp hadj).1
  have hwin := sideOuterCluster_subset_sideWindow m right X hvc
  have hinner : v.val.1 ≠ (if right then (m:ℤ) else -(m:ℤ)) := by
    intro h
    exact hno ⟨v,h,hvc⟩
  have hucoords := connectorNativeVertex_coordinates m hm X u
  have huwin : u.val ∈ sideWindow m right := by
    cases right <;> dsimp [sideWindow] at hwin ⊢ <;> dsimp at hinner <;> omega
  have hH : e.val ∈ (sideCensoredGraph m right).edgeSet := by
    rw [hpair]
    exact (sideCensoredGraph m right).mem_edgeSet.mpr ⟨hadj,huwin,hwin⟩
  let eH : (sideCensoredGraph m right).edgeSet := ⟨e.val,hH⟩
  have hincl : Thm3.Prop4.censoredEdgeInclusion (sideCensoredGraph_le m right) eH = e := rfl
  apply huc
  exact censoredSeedReveal_open_edge_endpoint_reached _ _ X eH (hincl ▸ he) (hincl ▸ hr) u.val hue

end
end PottsContinuity.Thm4Records
