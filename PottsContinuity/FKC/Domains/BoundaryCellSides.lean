-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/BoundaryCellSides.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCells
public import PottsContinuity.FKC.Medial.LatticePorts

/-!
# The two actual cells adjacent to a polygon edge

The canonical normalized unit bond has two genuine neighboring open square
cells. A fixed rational unit direction is transverse to every square-lattice
edge. Small positive and negative displacements from an edge midpoint lie in
the two cells; the proved polygon crossing-parity theorem then excludes their
lying on the same Jordan side. No side-flip premise is added.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge Medial Schoenflies

noncomputable section

def crossingVector : ℂ := ⟨3 / 5, 4 / 5⟩

def crossingDirection : Plane := complexPlaneCoordinates crossingVector

private theorem crossingDirection_unit : Plane.IsDirection crossingDirection := by
  have hs := Plane.norm_sq_eq crossingDirection
  change ‖crossingDirection‖ ^ 2 = (3 / 5 : ℝ) ^ 2 + (4 / 5 : ℝ) ^ 2 at hs
  norm_num at hs
  change ‖crossingDirection‖ = 1
  rcases hs with hs | hs
  · exact hs
  · linarith [norm_nonneg crossingDirection]

private theorem crossingDirection_transverse (δ : PositiveMesh) {u v : LatticeVertex}
    (huv : squareLattice.Adj u v) :
    hgt crossingDirection (complexPlaneCoordinates (latticeEmbed δ u)) ≠
      hgt crossingDirection (complexPlaneCoordinates (latticeEmbed δ v)) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  intro h
  change ((x + 1 = z ∨ z + 1 = x) ∧ y = w) ∨
    (x = z ∧ (y + 1 = w ∨ w + 1 = y)) at huv
  change (3 / 5 : ℝ) * (δ.val * (y : ℝ)) - (4 / 5 : ℝ) * (δ.val * (x : ℝ)) =
    (3 / 5 : ℝ) * (δ.val * (w : ℝ)) - (4 / 5 : ℝ) * (δ.val * (z : ℝ)) at h
  rcases huv with ⟨hstep | hstep, rfl⟩ | ⟨rfl, hstep | hstep⟩
  · subst z
    simp only [Int.cast_add, Int.cast_one] at h
    nlinarith [δ.property]
  · subst x
    simp only [Int.cast_add, Int.cast_one] at h
    nlinarith [δ.property]
  · subst w
    simp only [Int.cast_add, Int.cast_one] at h
    nlinarith [δ.property]
  · subst y
    simp only [Int.cast_add, Int.cast_one] at h
    nlinarith [δ.property]

private theorem coordinates_sub_crossing (z : ℂ) (t : ℝ) :
    complexPlaneCoordinates (z - t • crossingVector) =
      complexPlaneCoordinates z - t • crossingDirection := by
  change complexPlaneCoordinatesLinear (z - t • crossingVector) =
    complexPlaneCoordinatesLinear z - t • complexPlaneCoordinatesLinear crossingVector
  rw [map_sub, map_smul]

private theorem coordinates_add_crossing (z : ℂ) (t : ℝ) :
    complexPlaneCoordinates (z + t • crossingVector) =
      complexPlaneCoordinates z + t • crossingDirection := by
  change complexPlaneCoordinatesLinear (z + t • crossingVector) =
    complexPlaneCoordinatesLinear z + t • complexPlaneCoordinatesLinear crossingVector
  rw [map_add, map_smul]

namespace Medial.LatticeBond

/-- The actual bond midpoint agrees with the affine midpoint of its endpoints. -/
theorem midpoint_eq_affine (e : LatticeBond) (δ : PositiveMesh) :
    e.midpoint δ = _root_.midpoint ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) := by
  apply Complex.ext <;>
    simp [midpoint, midpoint_eq_smul_add, Complex.real_smul] <;> ring

private theorem midpoint_sub_crossing_mem (e : LatticeBond) (δ : PositiveMesh)
    {t : ℝ} (ht : 0 < t) (hδ : t < δ.val / 2) :
    e.midpoint δ - t • crossingVector ∈ openLatticeCell δ (e.faceBase false) := by
  rcases e with ⟨⟨x, y⟩, ax⟩
  cases ax <;>
    simp [mem_openLatticeCell_iff, midpoint, source, target, faceBase, latticeEmbed,
      crossingVector, Complex.real_smul] <;>
    constructor <;> constructor <;> nlinarith [δ.property]

private theorem midpoint_add_crossing_mem (e : LatticeBond) (δ : PositiveMesh)
    {t : ℝ} (ht : 0 < t) (hδ : t < δ.val / 2) :
    e.midpoint δ + t • crossingVector ∈ openLatticeCell δ (e.faceBase true) := by
  rcases e with ⟨⟨x, y⟩, ax⟩
  cases ax <;>
    simp [mem_openLatticeCell_iff, midpoint, source, target, faceBase, latticeEmbed,
      crossingVector, Complex.real_smul] <;>
    constructor <;> constructor <;> nlinarith [δ.property]

end Medial.LatticeBond

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- The unique normalized actual unit bond representing an original cyclic edge. -/
def boundaryBond (i : ZMod (m + 3)) : LatticeBond :=
  Classical.choose (LatticeBond.exists_of_adj (P.adjacent i))

theorem boundaryBond_toSym2 (i : ZMod (m + 3)) :
    (P.boundaryBond i).toSym2 = s(P.vertex i, P.vertex (i + 1)) :=
  Classical.choose_spec (LatticeBond.exists_of_adj (P.adjacent i))

theorem eq_boundaryBond_iff (i : ZMod (m + 3)) (e : LatticeBond) :
    e = P.boundaryBond i ↔ e.toSym2 = s(P.vertex i, P.vertex (i + 1)) := by
  rw [← P.boundaryBond_toSym2 i]
  exact LatticeBond.toSym2_injective.eq_iff.symm

private theorem midpoint_mem_polygon_openSegment (δ : PositiveMesh)
    (i : ZMod (m + 3)) (e : LatticeBond)
    (he : e.toSym2 = s(P.vertex i, P.vertex (i + 1))) :
    complexPlaneCoordinates (e.midpoint δ) ∈
      openSegment ℝ ((P.toPrePolygon δ).vertex i) ((P.toPrePolygon δ).vertex (i + 1)) := by
  have hm : complexPlaneCoordinates (e.midpoint δ) = _root_.midpoint ℝ
      (complexPlaneCoordinates (latticeEmbed δ e.source))
      (complexPlaneCoordinates (latticeEmbed δ e.target)) := by
    rw [e.midpoint_eq_affine δ]
    exact complexPlaneCoordinatesLinear.toAffineMap.map_midpoint _ _
  rw [hm]
  change _ ∈ openSegment ℝ (complexPlaneCoordinates (latticeEmbed δ (P.vertex i)))
    (complexPlaneCoordinates (latticeEmbed δ (P.vertex (i + 1))))
  rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]
    exact midpoint_mem_openSegment _ _
  · rw [hs, ht, midpoint_comm]
    exact midpoint_mem_openSegment _ _

private theorem crossingDirection_pieces (δ : PositiveMesh) :
    ∀ Q ∈ (P.toPrePolygon δ).pieces,
      hgt crossingDirection Q.1 ≠ hgt crossingDirection Q.2 := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := PrePolygon.exists_of_mem_pieces hQ
  exact crossingDirection_transverse δ (P.adjacent i)

private theorem plane_inside_of_domain (δ : PositiveMesh) {z : ℂ} (hz : z ∈ P.domain δ) :
    complexPlaneCoordinates z ∈ inside (P.toPrePolygon δ).carrier := by
  rw [← P.image_carrier]
  exact hz

private theorem plane_outside_of_exterior (δ : PositiveMesh) {z : ℂ} (hz : z ∈ P.exterior δ) :
    complexPlaneCoordinates z ∈ outside (P.toPrePolygon δ).carrier := by
  rw [← P.image_carrier]
  exact hz

/-- The two actual open unit cells adjacent to a boundary bond are on opposite
Jordan sides, with no choice of clockwise or counterclockwise orientation. -/
theorem boundary_bond_cells_opposite (δ : PositiveMesh) (i : ZMod (m + 3))
    (e : LatticeBond) (he : e.toSym2 = s(P.vertex i, P.vertex (i + 1))) :
    (openLatticeCell δ (e.faceBase false) ⊆ P.domain δ ∧
      openLatticeCell δ (e.faceBase true) ⊆ P.exterior δ) ∨
    (openLatticeCell δ (e.faceBase false) ⊆ P.exterior δ ∧
      openLatticeCell δ (e.faceBase true) ⊆ P.domain δ) := by
  obtain ⟨ε, hε, hflip⟩ := (P.toPrePolygon δ).parity_flip_carrier crossingDirection_unit
    (P.crossingDirection_pieces δ) i (P.midpoint_mem_polygon_openSegment δ i e he)
  obtain ⟨t, ht, htm⟩ := exists_between (lt_min hε (half_pos δ.property))
  have htε := htm.trans_le (min_le_left _ _)
  have htδ := htm.trans_le (min_le_right _ _)
  obtain ⟨_, _, hflip⟩ := hflip t ht htε
  rw [← coordinates_sub_crossing, ← coordinates_add_crossing] at hflip
  have hminus := e.midpoint_sub_crossing_mem δ ht htδ
  have hplus := e.midpoint_add_crossing_mem δ ht htδ
  rcases P.openLatticeCell_subset_domain_or_exterior δ (e.faceBase false) with hfi | hfo
  · rcases P.openLatticeCell_subset_domain_or_exterior δ (e.faceBase true) with hti | hto
    · rw [(P.toPrePolygon δ).parity_eq_one_of_mem_inside crossingDirection_unit
        (P.crossingDirection_pieces δ) (P.plane_inside_of_domain δ (hfi hminus)),
        (P.toPrePolygon δ).parity_eq_one_of_mem_inside crossingDirection_unit
        (P.crossingDirection_pieces δ) (P.plane_inside_of_domain δ (hti hplus))] at hflip
      exact ((by decide : (1 : ZMod 2) ≠ 1 + 1) hflip).elim
    · exact Or.inl ⟨hfi, hto⟩
  · rcases P.openLatticeCell_subset_domain_or_exterior δ (e.faceBase true) with hti | hto
    · exact Or.inr ⟨hfo, hti⟩
    · rw [(P.toPrePolygon δ).parity_eq_zero_of_mem_outside crossingDirection_unit
        (P.crossingDirection_pieces δ) (P.plane_outside_of_exterior δ (hfo hminus)),
        (P.toPrePolygon δ).parity_eq_zero_of_mem_outside crossingDirection_unit
        (P.crossingDirection_pieces δ) (P.plane_outside_of_exterior δ (hto hplus))] at hflip
      norm_num at hflip

theorem boundaryBond_cells_opposite (δ : PositiveMesh) (i : ZMod (m + 3)) :
    (openLatticeCell δ ((P.boundaryBond i).faceBase false) ⊆ P.domain δ ∧
      openLatticeCell δ ((P.boundaryBond i).faceBase true) ⊆ P.exterior δ) ∨
    (openLatticeCell δ ((P.boundaryBond i).faceBase false) ⊆ P.exterior δ ∧
      openLatticeCell δ ((P.boundaryBond i).faceBase true) ⊆ P.domain δ) :=
  P.boundary_bond_cells_opposite δ i (P.boundaryBond i) (P.boundaryBond_toSym2 i)

/-- Exactly one of the two geometric cells lies in the actual unbounded exterior. -/
theorem boundaryBond_existsUnique_outside_cell (δ : PositiveMesh) (i : ZMod (m + 3)) :
    ∃! side : Bool, openLatticeCell δ ((P.boundaryBond i).faceBase side) ⊆ P.exterior δ := by
  rcases P.boundaryBond_cells_opposite δ i with ⟨hfi, hto⟩ | ⟨hfo, hti⟩
  · refine ⟨true, hto, ?_⟩
    intro side hside
    cases side
    · exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
        (hfi (latticeCellCenter_mem δ _)) (hside (latticeCellCenter_mem δ _))).elim
    · rfl
  · refine ⟨false, hfo, ?_⟩
    intro side hside
    cases side
    · rfl
    · exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
        (hti (latticeCellCenter_mem δ _)) (hside (latticeCellCenter_mem δ _))).elim

end LatticePolygon
end

end PottsContinuity.FKC
