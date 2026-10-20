-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygon.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeEdges
public import PottsContinuity.FKC.SLEWrap.Geometry.ComplexJordanExtension
public import Schoenflies.PrePolygonSep

/-!
# Simple nearest-neighbor lattice polygons

A polygon is a cyclic list of distinct lattice vertices joined by unit lattice
edges. The unit-edge intersection theorem proves that its Euclidean embedding
is simple. The resulting `PrePolygon` permits collinear consecutive edges and
therefore retains every boundary lattice vertex, including straight runs.
The Jordan and separation properties below are conclusions, not carrier fields.
-/

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

open Set
open OAI.SLEExactGauge

/-- The existing complex coordinate chart, with its actual real linearity bundled. -/
def complexPlaneCoordinatesLinear : ℂ ≃ₗ[ℝ] Schoenflies.Plane where
  toEquiv := complexPlaneCoordinates.toEquiv
  map_add' z w := by
    ext i
    fin_cases i <;> rfl
  map_smul' r z := by
    ext i
    fin_cases i
    · change (r • z).re = r * z.re
      simp
    · change (r • z).im = r * z.im
      simp

theorem complexPlaneCoordinates_image_segment (z w : ℂ) :
    complexPlaneCoordinates '' segment ℝ z w =
      segment ℝ (complexPlaneCoordinates z) (complexPlaneCoordinates w) :=
  image_segment ℝ complexPlaneCoordinatesLinear.toLinearMap.toAffineMap z w

/-- A cyclic simple nearest-neighbor lattice polygon. Simplicity of its
Euclidean segments will be proved, rather than included as an extra field. -/
structure LatticePolygon (m : ℕ) where
  vertex : ZMod (m + 3) → LatticeVertex
  vertex_injective : Function.Injective vertex
  adjacent : ∀ i, squareLattice.Adj (vertex i) (vertex (i + 1))

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- Distinct cyclic indices never describe the same unoriented lattice edge. -/
theorem edge_ne {i j : ZMod (m + 3)} (hij : i ≠ j) :
    s(P.vertex i, P.vertex (i + 1)) ≠ s(P.vertex j, P.vertex (j + 1)) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hij (P.vertex_injective h₁)
  · have h₁' := P.vertex_injective h₁
    have h₂' := P.vertex_injective h₂
    apply Schoenflies.PrePolygon.two_ne_zero' (m := m)
    linear_combination h₂' - h₁'

/-- The actual geometric boundary: the union of the closed embedded unit edges. -/
def carrier (δ : PositiveMesh) : Set ℂ :=
  ⋃ i, segment ℝ (latticeEmbed δ (P.vertex i)) (latticeEmbed δ (P.vertex (i + 1)))

theorem edge_subset_carrier (δ : PositiveMesh) (i : ZMod (m + 3)) :
    segment ℝ (latticeEmbed δ (P.vertex i)) (latticeEmbed δ (P.vertex (i + 1))) ⊆
      P.carrier δ := by
  exact subset_iUnion (fun j =>
    segment ℝ (latticeEmbed δ (P.vertex j)) (latticeEmbed δ (P.vertex (j + 1)))) i

theorem vertex_mem_carrier (δ : PositiveMesh) (i : ZMod (m + 3)) :
    latticeEmbed δ (P.vertex i) ∈ P.carrier δ :=
  P.edge_subset_carrier δ i (left_mem_segment ℝ _ _)

/-- The embedded polygon with all boundary lattice vertices retained. The
geometric simplicity field is derived from distinct unit lattice edges. -/
def toPrePolygon (δ : PositiveMesh) : Schoenflies.PrePolygon m where
  vertex i := complexPlaneCoordinates (latticeEmbed δ (P.vertex i))
  vertex_inj := complexPlaneCoordinates.injective.comp
    ((latticeEmbed_injective δ).comp P.vertex_injective)
  edges_meet i j hij := by
    intro z hz
    rw [← complexPlaneCoordinates_image_segment, ← complexPlaneCoordinates_image_segment,
      ← image_inter complexPlaneCoordinates.injective] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases (mem_inter_lattice_segments_endpoints δ (P.adjacent i) (P.adjacent j)
      (P.edge_ne hij) hw).1 with h | h
    · simp [h]
    · simp [h]

/-- Coordinate transport preserves the entire union of closed boundary edges. -/
theorem image_carrier (δ : PositiveMesh) :
    complexPlaneCoordinates '' P.carrier δ = (P.toPrePolygon δ).carrier := by
  simp only [carrier, image_iUnion, complexPlaneCoordinates_image_segment,
    Schoenflies.PrePolygon.carrier, Schoenflies.PrePolygon.edge, toPrePolygon]

/-- Every positive-mesh embedding of the lattice polygon is a genuine Jordan curve. -/
theorem isJordanCurve_carrier (δ : PositiveMesh) :
    Schoenflies.IsJordanCurve (complexPlaneCoordinates '' P.carrier δ) := by
  rw [P.image_carrier]
  exact (P.toPrePolygon δ).isJordanCurve_carrier

/-- The boundary has the two actual complementary regions supplied by the
polygonal Jordan theorem; the bounded region is not assumed as extra data. -/
theorem isSeparating_carrier (δ : PositiveMesh) :
    Schoenflies.IsSeparating (complexPlaneCoordinates '' P.carrier δ) := by
  rw [P.image_carrier]
  exact (P.toPrePolygon δ).isSeparating_carrier

end LatticePolygon
end
end PottsContinuity.FKC
