-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonInteriorNeighbor.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.PolygonDomain
public import PottsContinuity.FKC.Domains.LatticeEdges
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set OAI.SLEExactGauge

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- A unit lattice segment can meet the polygon carrier only at its endpoints
when its initial endpoint is in the actual Jordan interior. -/
private theorem latticeSegment_carrier_inter_subset_endpoints (δ : PositiveMesh)
    {u v : LatticeVertex} (huv : squareLattice.Adj u v)
    (hu : latticeEmbed δ u ∈ P.domain δ) :
    segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ∩ P.carrier δ ⊆
      {latticeEmbed δ u, latticeEmbed δ v} := by
  intro z hz
  obtain ⟨hzSeg, hzCarrier⟩ := hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzCarrier
  let C : Set Schoenflies.Plane := complexPlaneCoordinates '' P.carrier δ
  have huInside : complexPlaneCoordinates (latticeEmbed δ u) ∈
      Schoenflies.inside C := by
    change complexPlaneCoordinates (latticeEmbed δ u) ∈
      Schoenflies.inside (complexPlaneCoordinates '' P.carrier δ)
    exact hu
  have huNotCarrier : complexPlaneCoordinates (latticeEmbed δ u) ∉ C :=
    (Schoenflies.mem_inside_iff.mp huInside).1
  have hedges : s(u, v) ≠ s(P.vertex i, P.vertex (i + 1)) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h₁, _⟩ | ⟨h₁, _⟩
    · apply huNotCarrier
      exact mem_image_of_mem _ (h₁ ▸ P.vertex_mem_carrier δ i)
    · apply huNotCarrier
      exact mem_image_of_mem _ (h₁ ▸ P.vertex_mem_carrier δ (i + 1))
  rcases (mem_inter_lattice_segments_endpoints δ huv (P.adjacent i) hedges
      ⟨hzSeg, hi⟩).1 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Every open point of a lattice edge leaving an interior lattice vertex remains
in the actual polygon domain. The proof uses the Jordan complementary component:
the open edge misses the carrier and is connected to an interior point near its
initial endpoint. -/
theorem openSegment_to_neighbor_subset_domain (δ : PositiveMesh)
    {u v : LatticeVertex} (huv : squareLattice.Adj u v)
    (hu : latticeEmbed δ u ∈ P.domain δ) :
    openSegment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ⊆ P.domain δ := by
  let S : Set ℂ := openSegment ℝ (latticeEmbed δ u) (latticeEmbed δ v)
  let C : Set Schoenflies.Plane := complexPlaneCoordinates '' P.carrier δ
  have hne : latticeEmbed δ u ≠ latticeEmbed δ v := by
    intro h
    exact huv.ne (latticeEmbed_injective δ h)
  have havoid : S ⊆ (P.carrier δ)ᶜ := by
    intro z hz hzC
    have hzSeg : z ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) :=
      openSegment_subset_segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) hz
    have hzEndpoints := P.latticeSegment_carrier_inter_subset_endpoints δ huv hu
      ⟨hzSeg, hzC⟩
    rcases hzEndpoints with h | h
    · subst z
      exact hne (left_mem_openSegment_iff.mp hz)
    · subst z
      exact hne (right_mem_openSegment_iff.mp hz)
  have hSpre : IsPreconnected S :=
    (convex_openSegment (latticeEmbed δ u) (latticeEmbed δ v)).isPreconnected
  have hScoord : IsPreconnected (complexPlaneCoordinates '' S) :=
    hSpre.image complexPlaneCoordinates complexPlaneCoordinates.continuous.continuousOn
  have hSavoid : complexPlaneCoordinates '' S ⊆ Cᶜ := by
    rintro z ⟨w, hw, rfl⟩ hzC
    rcases hzC with ⟨y, hy, heq⟩
    have hyw : y = w := complexPlaneCoordinates.injective heq
    subst y
    exact havoid hw hy
  have huClosure : latticeEmbed δ u ∈ closure S := by
    exact segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
  have huMeetClosure : latticeEmbed δ u ∈ closure (P.domain δ ∩ S) :=
    (P.isJordanDomain δ).isOpen.inter_closure ⟨hu, huClosure⟩
  have hmeet : (P.domain δ ∩ S).Nonempty :=
    Set.Nonempty.of_closure ⟨latticeEmbed δ u, huMeetClosure⟩
  obtain ⟨z, hzMeet⟩ := hmeet
  have hzDomain : z ∈ P.domain δ := hzMeet.1
  have hzS : z ∈ S := hzMeet.2
  have hzInside : complexPlaneCoordinates z ∈ Schoenflies.inside C := by
    change z ∈ complexInside (P.carrier δ) at hzDomain
    exact hzDomain
  have hzComp := (Schoenflies.mem_inside_iff.mp hzInside).2
  have hzCoordS : complexPlaneCoordinates z ∈ complexPlaneCoordinates '' S :=
    mem_image_of_mem _ hzS
  have hsub := hScoord.subset_connectedComponentIn hzCoordS hSavoid
  intro w hwS
  have hwCoord : complexPlaneCoordinates w ∈ complexPlaneCoordinates '' S :=
    mem_image_of_mem _ hwS
  have hwComp : complexPlaneCoordinates w ∈
      connectedComponentIn Cᶜ (complexPlaneCoordinates z) := hsub hwCoord
  have hcomponentEq := connectedComponentIn_eq hwComp
  have hwInside : complexPlaneCoordinates w ∈ Schoenflies.inside C := by
    apply Schoenflies.mem_inside_iff.mpr
    constructor
    · exact hSavoid hwCoord
    · rw [← hcomponentEq]
      exact hzComp
  change w ∈ complexInside (P.carrier δ)
  exact hwInside

theorem interior_neighbor_segment_subset_closure (δ : PositiveMesh)
    {u v : LatticeVertex} (huv : squareLattice.Adj u v)
    (hu : latticeEmbed δ u ∈ P.domain δ) :
    segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ⊆ closure (P.domain δ) := by
  exact (segment_subset_closure_openSegment (x := latticeEmbed δ u)
      (y := latticeEmbed δ v)).trans
    (closure_mono (P.openSegment_to_neighbor_subset_domain δ huv hu))

end

end PottsContinuity.FKC.LatticePolygon
