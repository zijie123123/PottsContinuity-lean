module

public import PottsContinuity.Thm4Records.NativeInteriorStar
public import PottsContinuity.Thm4Records.SideNativeAttachment
public import PottsContinuity.Thm4Records.NativeReference

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- The local root reveal is disjoint from vertices of the native square. -/
theorem ballQuery_no_native_attachment (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (he : e ∈ slitScreenBallReveal m X)
    (u : connectorNativeVertex m hm X) : u.val ∉ e.val := by
  intro hue
  have hball : ∀ v ∈ e.val, Thm4Side.slitScreenRadius m v ≤ (m:ℤ) := by
    simpa only [slitScreenBallReveal,slitScreenBallRevealEdges,Finset.mem_filter,
      Finset.mem_univ,true_and] using he
  have hb := hball u.val hue
  change max |u.val.val.1| |u.val.val.2+(16*m:ℤ)| ≤ (m:ℤ) at hb
  have h := (abs_le.mp ((le_max_right _ _).trans hb)).2
  have hc := connectorNativeVertex_coordinates m hm X u
  omega

/-- Every queried open bond attaches to the true native carrier only on the
top or bottom row when neither outer primal cluster reaches the inner side. -/
theorem connectorOpenQuery_native_endpoint_on_topBottom_of_no_primal_connections
    (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hleft : X ∉ sidePrimalConnectionEvent m false)
    (hright : X ∉ sidePrimalConnectionEvent m true)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (he : e ∈ (revealRecordConfiguration (connectorReveal m hm) X).val)
    (u : connectorNativeVertex m hm X) (hu : u.val ∈ e.val) :
    u ∈ connectorNativeTopBottom m hm X := by
  classical
  have he' : e ∈ X ∧ e ∈ connectorReveal m hm X := by
    simpa only [revealRecordConfiguration,Finset.mem_inter] using he
  have hc := connectorNativeVertex_coordinates m hm X u
  by_contra hnot
  have hy : -(12*(m:ℤ)) < u.val.val.2 ∧ u.val.val.2 < -(2*(m:ℤ)) := by
    change ¬ (u.val.val.2=-(12*(m:ℤ)) ∨ u.val.val.2=-(2*(m:ℤ))) at hnot
    omega
  have hr : e ∈ slitScreenBallReveal m X ∨
      e ∈ sideOuterClusterReveal m false X ∨
      e ∈ sideOuterClusterReveal m true X ∨ e ∈ exteriorRevealEdges m hm := by
    simpa only [connectorReveal,connectorClusterReveal,sideJointReveal,jointReveal,
      Finset.mem_union,or_assoc] using he'.2
  rcases hr with hball | hleft' | hright' | hext
  · exact ballQuery_no_native_attachment m hm X e hball u hu
  · exact sideOpenQuery_no_native_attachment_of_no_primal_connection m hm false X hleft
      e he'.1 hleft' u hu
  · exact sideOpenQuery_no_native_attachment_of_no_primal_connection m hm true X hright
      e he'.1 hright' u hu
  · have hex : e ∉ rStarSourceEdges m hm := by
      simpa only [exteriorRevealEdges,Finset.mem_sdiff,Finset.mem_univ,true_and] using hext
    exact hex (source_edge_interior_mem_rStarSourceEdges m hm e u.val hu ⟨hc.1,hc.2.1⟩ hy)

/-- The actual induced primal partition has the prescribed upper bound.
All geometry refers to original queried bonds and incident native vertices. -/
theorem connectorIncidentBoundary_le_topBottom_of_no_primal_connections
    (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hleft : X ∉ sidePrimalConnectionEvent m false)
    (hright : X ∉ sidePrimalConnectionEvent m true) :
    (connectorIncidentBoundary m hm X
      (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))).partition ≤
      (BoundaryCondition.wired (connectorNativeTopBottom m hm X)).partition := by
  apply connectorIncidentBoundary_le_topBottom_of_endpoint_attachment
  · exact connectorOpenQuery_native_endpoint_on_topBottom_of_no_primal_connections
      m hm X hleft hright
  · intro u hu
    exact False.elim (connectorNativeVertex_not_slitBoundary m hm X u hu)

/-- The square estimate holds under the literal induced native law whenever
the two outer clusters fail to cross their respective censored windows. -/
theorem connectorIncidentNoncrossing_lower_of_no_primal_connections
    (m : ℕ) (hm : 1 ≤ m) (q : Set.Ici (1:ℝ))
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hleft : X ∉ sidePrimalConnectionEvent m false)
    (hright : X ∉ sidePrimalConnectionEvent m true) :
    1/(1+(q:ℝ)^2) ≤
      (measure (connectorIncidentGraph m hm X) (criticalParameters q)
        (connectorIncidentBoundary m hm X
          (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m))))
        (connectorNativeVertical m hm X)ᶜ).toReal :=
  connectorIncidentNoncrossing_lower_of_partition_order m hm q X _
    (connectorIncidentBoundary_le_topBottom_of_no_primal_connections m hm X hleft hright)

end
end PottsContinuity.Thm4Records
