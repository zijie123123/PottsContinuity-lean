module

public import PottsContinuity.Thm4Plane.ScreenTargetCapGraphConnectivity
public import PottsContinuity.Thm4Plane.ScreenTargetCapInducedPath

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK

/-- The component of the clipped cap center after deleting the bonds in `R`. -/
def screenTargetCapEdgeDeletedComponent (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m))) :
    Set (SlitBoxVertex (16 * m)) :=
  {v | (edgeRestriction (slitBoxGraph (16 * m)) R).Reachable
    (slitBoxBottomCenterVertex (16 * m)) v}

/-- If the removed bonds have no endpoints pair inside the cap, the canonical
edge-deleted component contains every vertex of the cap. -/
theorem screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal
    (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (slitBoxGraph (16 * m)))
    (hR : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e) :
    screenTargetCap m ⊆ screenTargetCapEdgeDeletedComponent m R := by
  intro v hv
  change (edgeRestriction (slitBoxGraph (16 * m)) R).Reachable
    (slitBoxBottomCenterVertex (16 * m)) v
  let c : screenTargetCap m :=
    ⟨slitBoxBottomCenterVertex (16 * m), screenTargetCap_bottomCenter_mem m⟩
  let w : screenTargetCap m := ⟨v, hv⟩
  exact screenTargetCap_reachable_in_edgeRestriction_of_no_internal_removal
    m hm R hR c w

/-- Every original bond leaving the component obtained by deleting `R` is
itself among the deleted bonds. -/
theorem screenTargetCapEdgeDeletedComponent_boundaryEdge_mem_removed
    (m : ℕ) (R : Configuration (slitBoxGraph (16 * m)))
    (u v : SlitBoxVertex (16 * m))
    (hu : u ∈ screenTargetCapEdgeDeletedComponent m R)
    (hv : v ∉ screenTargetCapEdgeDeletedComponent m R)
    (hAdj : (slitBoxGraph (16 * m)).Adj u v) :
    (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hAdj⟩ :
      (slitBoxGraph (16 * m)).edgeSet) ∈ R := by
  let G := slitBoxGraph (16 * m)
  let H := edgeRestriction G R
  have hbase : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr hAdj
  by_contra hnot
  have hHedge : s(u, v) ∈ H.edgeSet := by
    rw [edgeRestriction_edgeSet]
    refine ⟨hbase, ?_⟩
    intro hopen
    exact hnot ((coe_mem_openEdges_iff G R ⟨s(u, v), hbase⟩).mp hopen)
  have hHAdj : H.Adj u v := H.mem_edgeSet.mpr hHedge
  have huReach : H.Reachable (slitBoxBottomCenterVertex (16 * m)) u := hu
  have hvReach : H.Reachable (slitBoxBottomCenterVertex (16 * m)) v :=
    huReach.trans hHAdj.reachable
  exact hv hvReach

end PottsContinuity.Thm4Plane
