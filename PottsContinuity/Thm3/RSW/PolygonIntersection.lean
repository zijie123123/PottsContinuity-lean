module

public import PottsContinuity.PlanarTopology.BoundedOpenGeometry
public import PottsContinuity.FKC.Domains.PolygonDomain

/-!
# Intersection of overlapping, nonnested polygon interiors

The P5b annulus chain requires an actual common boundary vertex. This module
proves the topological frontier-intersection step. The coordinate estimates
showing that neighboring annulus polygons are nonnested are proved in
`Thm3.RSW.AdjacentAnnulusPolygons` (`adjacent_annulus_polygons_shared_vertex`).
-/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- Overlapping open regions with connected first interior and connected
second frontier must have intersecting frontiers if each frontier has a point
outside the other region's closure. -/
theorem frontier_inter_nonempty_of_overlap_nonnesting
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hconn : IsPreconnected U)
    (hfront : IsPreconnected (frontier V)) (hoverlap : (U ∩ V).Nonempty)
    (houtU : ∃ x ∈ frontier U, x ∉ closure V)
    (houtV : ∃ x ∈ frontier V, x ∉ closure U) :
    (frontier U ∩ frontier V).Nonempty := by
  by_contra hnone
  have hd : Disjoint (frontier U) (frontier V) :=
    Set.disjoint_left.mpr (fun x hx hy => hnone ⟨x,hx,hy⟩)
  have hint : (frontier V ∩ U).Nonempty := by
    by_contra hn
    have hd' : Disjoint U (frontier V) :=
      Set.disjoint_left.mpr (fun x hx hy => hn ⟨x,hy,hx⟩)
    have hsub := PlanarTopology.subset_open_of_preconnected_frontier_disjoint
      hconn hV hd' hoverlap
    obtain ⟨x,hx,hnot⟩ := houtU
    exact hnot (closure_mono hsub hx.1)
  have hsub := PlanarTopology.subset_open_of_preconnected_frontier_disjoint
    hfront hU hd.symm hint
  obtain ⟨x,hx,hnot⟩ := houtV
  exact hnot (subset_closure (hsub hx))

/-- A genuine lattice polygon's whole geometric carrier is connected. -/
theorem latticePolygon_carrier_isConnected {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) : IsConnected (P.carrier δ) := by
  have h := (P.isJordanCurve_carrier δ).isConnected.image
    OAI.SLEExactGauge.complexPlaneCoordinates.symm
    OAI.SLEExactGauge.complexPlaneCoordinates.symm.continuous.continuousOn
  simp only [Set.image_image,Homeomorph.symm_apply_apply] at h
  change IsConnected (id '' P.carrier δ) at h
  simpa only [Set.image_id] using h

/-- The Jordan boundaries of two overlapping polygon interiors intersect once
actual points outside each other's closure are supplied. -/
theorem latticePolygon_carriers_inter_of_overlapNonnesting
    {m k : ℕ} (P : FKC.LatticePolygon m) (Q : FKC.LatticePolygon k)
    (δ : FKC.PositiveMesh) (hoverlap : (P.domain δ ∩ Q.domain δ).Nonempty)
    (houtP : ∃ z ∈ P.carrier δ, z ∉ closure (Q.domain δ))
    (houtQ : ∃ z ∈ Q.carrier δ, z ∉ closure (P.domain δ)) :
    (P.carrier δ ∩ Q.carrier δ).Nonempty := by
  have h := frontier_inter_nonempty_of_overlap_nonnesting (P.domain δ) (Q.domain δ)
    (P.isJordanDomain δ).isOpen (Q.isJordanDomain δ).isOpen
    (P.isJordanDomain δ).isConnected.isPreconnected
    (by rw [Q.frontier_domain]; exact (latticePolygon_carrier_isConnected Q δ).isPreconnected)
    hoverlap (by simpa only [P.frontier_domain] using houtP)
    (by simpa only [Q.frontier_domain] using houtQ)
  simpa only [P.frontier_domain,Q.frontier_domain] using h

end PottsContinuity.RSW
