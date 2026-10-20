-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/DomainBondSides.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.InteriorCorners
public import PottsContinuity.FKC.Domains.BoundaryCellSides

/-!
# Exhaustive Jordan-side classification of actual domain bonds

A unit bond midpoint belongs to the polygon carrier exactly when the bond is
one of its original cyclic edges. Otherwise an actual domain bond has its
midpoint in the open Jordan domain. Each adjacent cell accumulates at that
midpoint, so both cells meet the domain and hence lie entirely inside it.
Together with the proved boundary-side crossing result this classifies all
actual domain bonds, without an additional side or edge-existence hypothesis.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set Medial

noncomputable section

namespace Medial.LatticeBond

/-- The actual bond midpoint belongs to its complete closed segment. -/
theorem midpoint_mem_segment (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ ∈ segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) := by
  rw [e.midpoint_eq_affine δ]
  exact _root_.midpoint_mem_segment _ _

theorem midpoint_ne_source (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ ≠ latticeEmbed δ e.source := by
  rw [e.midpoint_eq_affine δ]
  exact fun h => e.source_ne_target
    (latticeEmbed_injective δ ((midpoint_eq_left_iff ℝ).mp h))

theorem midpoint_ne_target (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ ≠ latticeEmbed δ e.target := by
  rw [e.midpoint_eq_affine δ]
  exact fun h => e.source_ne_target
    (latticeEmbed_injective δ ((midpoint_eq_right_iff ℝ).mp h))

/-- Both actual adjacent open cells accumulate at the edge midpoint. -/
theorem midpoint_mem_closure_cell (e : LatticeBond) (δ : PositiveMesh) (side : Bool) :
    e.midpoint δ ∈ closure (openLatticeCell δ (e.faceBase side)) :=
  port_segment_subset_closure_cell δ ⟨e, false, side⟩ (e.midpoint_mem_segment δ)

end Medial.LatticeBond

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

theorem boundaryBond_segment_subset_carrier (δ : PositiveMesh) (i : ZMod (m + 3)) :
    segment ℝ (latticeEmbed δ (P.boundaryBond i).source)
      (latticeEmbed δ (P.boundaryBond i).target) ⊆ P.carrier δ := by
  rcases Sym2.eq_iff.mp (P.boundaryBond_toSym2 i) with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]
    exact P.edge_subset_carrier δ i
  · rw [hs, ht, segment_symm]
    exact P.edge_subset_carrier δ i

/-- A strict bond midpoint is on the boundary exactly for original polygon edges. -/
theorem midpoint_mem_carrier_iff_boundaryBond (δ : PositiveMesh) (e : LatticeBond) :
    e.midpoint δ ∈ P.carrier δ ↔ ∃ i, e = P.boundaryBond i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    refine ⟨i, ?_⟩
    by_contra hne
    have hsym : s(e.source, e.target) ≠ s(P.vertex i, P.vertex (i + 1)) := by
      intro hsym
      exact hne ((P.eq_boundaryBond_iff i e).mpr hsym)
    have he := (mem_inter_lattice_segments_endpoints δ e.adjacent (P.adjacent i)
      hsym ⟨e.midpoint_mem_segment δ, hi⟩).1
    exact he.elim (e.midpoint_ne_source δ) (e.midpoint_ne_target δ)
  · rintro ⟨i, rfl⟩
    exact P.boundaryBond_segment_subset_carrier δ i
      ((P.boundaryBond i).midpoint_mem_segment δ)

/-- Every cell adjacent to a midpoint in the actual open domain lies wholly inside. -/
theorem bond_cell_subset_domain_of_midpoint_mem (δ : PositiveMesh) (e : LatticeBond)
    (he : e.midpoint δ ∈ P.domain δ) (side : Bool) :
    openLatticeCell δ (e.faceBase side) ⊆ P.domain δ := by
  obtain ⟨z, hzD, hzc⟩ := mem_closure_iff.mp (e.midpoint_mem_closure_cell δ side)
    (P.domain δ) (P.isJordanDomain δ).isOpen he
  apply (P.openLatticeCell_subset_domain_iff_center δ (e.faceBase side)).mpr
  exact (P.openLatticeCell_mem_domain_iff_center δ (e.faceBase side) hzc).mp hzD

/-- An actual nonboundary domain bond has a strict midpoint in the Jordan interior. -/
theorem domainBond_midpoint_mem_domain_of_not_boundary (δ : PositiveMesh)
    (e : DomainBond δ (P.domain δ)) (he : ∀ i, e.val ≠ P.boundaryBond i) :
    e.val.midpoint δ ∈ P.domain δ := by
  have hm := e.property (e.val.midpoint_mem_segment δ)
  have hm : e.val.midpoint δ ∈ P.domain δ ∪ P.carrier δ := by
    simpa only [P.closure_domain] using hm
  rcases hm with hm | hm
  · exact hm
  · obtain ⟨i, hi⟩ := (P.midpoint_mem_carrier_iff_boundaryBond δ e.val).mp hm
    exact (he i hi).elim

/-- Both sides of every actual nonboundary domain bond are genuine interior cells. -/
theorem domainBond_cells_inside_of_not_boundary (δ : PositiveMesh)
    (e : DomainBond δ (P.domain δ)) (he : ∀ i, e.val ≠ P.boundaryBond i) (side : Bool) :
    openLatticeCell δ (e.val.faceBase side) ⊆ P.domain δ :=
  P.bond_cell_subset_domain_of_midpoint_mem δ e.val
    (P.domainBond_midpoint_mem_domain_of_not_boundary δ e he) side

/-- An exterior cell at an actual domain bond can occur only on an original polygon edge. -/
theorem domainBond_boundary_of_outside_cell (δ : PositiveMesh)
    (e : DomainBond δ (P.domain δ)) (side : Bool)
    (he : openLatticeCell δ (e.val.faceBase side) ⊆ P.exterior δ) :
    ∃ i, e.val = P.boundaryBond i := by
  classical
  by_contra h
  have hi := P.domainBond_cells_inside_of_not_boundary δ e
    (fun i hi => h ⟨i, hi⟩) side
  exact Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
    (hi (latticeCellCenter_mem δ _)) (he (latticeCellCenter_mem δ _))

end LatticePolygon
end
end PottsContinuity.FKC
