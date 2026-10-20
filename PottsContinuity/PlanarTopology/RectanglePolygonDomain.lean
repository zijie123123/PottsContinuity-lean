module

public import PottsContinuity.PlanarTopology.RectanglePolygon
public import PottsContinuity.PlanarTopology.BoundedOpenGeometry
public import PottsContinuity.FKC.Domains.PolygonDomain

@[expose] public section

namespace PottsContinuity.PlanarTopology
open Set

/-- With both side lengths at least two, adjacent rectangle-boundary lattice
vertices lie on one common side. The length-one cases would allow chords. -/
theorem rectangle_boundary_adj_common_side (a b u v : FKC.LatticeVertex)
    (hw : a.1+2 ≤ b.1) (hh : a.2+2 ≤ b.2)
    (hu : a.1 ≤ u.1 ∧ u.1 ≤ b.1 ∧ a.2 ≤ u.2 ∧ u.2 ≤ b.2 ∧
      (u.1 = a.1 ∨ u.1 = b.1 ∨ u.2 = a.2 ∨ u.2 = b.2))
    (hv : a.1 ≤ v.1 ∧ v.1 ≤ b.1 ∧ a.2 ≤ v.2 ∧ v.2 ≤ b.2 ∧
      (v.1 = a.1 ∨ v.1 = b.1 ∨ v.2 = a.2 ∨ v.2 = b.2))
    (hadj : FKC.squareLattice.Adj u v) :
    (u.1 = a.1 ∧ v.1 = a.1) ∨ (u.1 = b.1 ∧ v.1 = b.1) ∨
      (u.2 = a.2 ∧ v.2 = a.2) ∨ (u.2 = b.2 ∧ v.2 = b.2) := by
  rw [FKC.squareLattice_adj_iff] at hadj
  rcases hadj with h | h <;> omega

/-- An actual unit segment between such boundary vertices stays on the literal
continuous rectangle boundary, at every positive mesh. -/
theorem rectangle_boundary_segment_subset (δ : FKC.PositiveMesh)
    (a b u v : FKC.LatticeVertex) (hw : a.1+2 ≤ b.1) (hh : a.2+2 ≤ b.2)
    (hu : a.1 ≤ u.1 ∧ u.1 ≤ b.1 ∧ a.2 ≤ u.2 ∧ u.2 ≤ b.2 ∧
      (u.1 = a.1 ∨ u.1 = b.1 ∨ u.2 = a.2 ∨ u.2 = b.2))
    (hv : a.1 ≤ v.1 ∧ v.1 ≤ b.1 ∧ a.2 ≤ v.2 ∧ v.2 ≤ b.2 ∧
      (v.1 = a.1 ∨ v.1 = b.1 ∨ v.2 = a.2 ∨ v.2 = b.2))
    (hadj : FKC.squareLattice.Adj u v) :
    segment ℝ (FKC.latticeEmbed δ u) (FKC.latticeEmbed δ v) ⊆
      complexRectangleBoundary (δ.val*(a.1 : ℝ)) (δ.val*(b.1 : ℝ))
        (δ.val*(a.2 : ℝ)) (δ.val*(b.2 : ℝ)) := by
  let K : Set ℂ := Complex.re ⁻¹' Icc (δ.val*(a.1 : ℝ)) (δ.val*(b.1 : ℝ)) ∩
    Complex.im ⁻¹' Icc (δ.val*(a.2 : ℝ)) (δ.val*(b.2 : ℝ))
  have hconv : Convex ℝ K :=
    ((convex_Icc _ _).linear_preimage Complex.reLm).inter
      ((convex_Icc _ _).linear_preimage Complex.imLm)
  have hmem : ∀ z : FKC.LatticeVertex,
      a.1 ≤ z.1 → z.1 ≤ b.1 → a.2 ≤ z.2 → z.2 ≤ b.2 → FKC.latticeEmbed δ z ∈ K := by
    intro z hx0 hx1 hy0 hy1
    change (δ.val*(a.1 : ℝ) ≤ δ.val*(z.1 : ℝ) ∧
      δ.val*(z.1 : ℝ) ≤ δ.val*(b.1 : ℝ)) ∧
      (δ.val*(a.2 : ℝ) ≤ δ.val*(z.2 : ℝ) ∧ δ.val*(z.2 : ℝ) ≤ δ.val*(b.2 : ℝ))
    constructor <;> constructor
    all_goals apply mul_le_mul_of_nonneg_left _ δ.property.le
    · exact_mod_cast hx0
    · exact_mod_cast hx1
    · exact_mod_cast hy0
    · exact_mod_cast hy1
  intro z hz
  have hK := hconv.segment_subset (hmem u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1)
    (hmem v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1) hz
  refine ⟨hK.1.1,hK.1.2,hK.2.1,hK.2.2,?_⟩
  rcases rectangle_boundary_adj_common_side a b u v hw hh hu hv hadj with
    ⟨huv,hvv⟩ | ⟨huv,hvv⟩ | ⟨huv,hvv⟩ | ⟨huv,hvv⟩
  · left
    exact ((convex_singleton (δ.val*(a.1 : ℝ))).linear_preimage Complex.reLm).segment_subset
      (by change (FKC.latticeEmbed δ u).re = _; simp only [FKC.latticeEmbed_re,huv])
      (by change (FKC.latticeEmbed δ v).re = _; simp only [FKC.latticeEmbed_re,hvv]) hz
  · right; left
    exact ((convex_singleton (δ.val*(b.1 : ℝ))).linear_preimage Complex.reLm).segment_subset
      (by change (FKC.latticeEmbed δ u).re = _; simp only [FKC.latticeEmbed_re,huv])
      (by change (FKC.latticeEmbed δ v).re = _; simp only [FKC.latticeEmbed_re,hvv]) hz
  · right; right; left
    exact ((convex_singleton (δ.val*(a.2 : ℝ))).linear_preimage Complex.imLm).segment_subset
      (by change (FKC.latticeEmbed δ u).im = _; simp only [FKC.latticeEmbed_im,huv])
      (by change (FKC.latticeEmbed δ v).im = _; simp only [FKC.latticeEmbed_im,hvv]) hz
  · right; right; right
    exact ((convex_singleton (δ.val*(b.2 : ℝ))).linear_preimage Complex.imLm).segment_subset
      (by change (FKC.latticeEmbed δ u).im = _; simp only [FKC.latticeEmbed_im,huv])
      (by change (FKC.latticeEmbed δ v).im = _; simp only [FKC.latticeEmbed_im,hvv]) hz

/-- All genuine unit boundary edges of the explicit rectangle polygon lie
on the four literal continuous rectangle sides. -/
theorem rectangleLatticePolygon_carrier_subset (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh) :
    (rectangleLatticePolygon a w h (by omega) (by omega)).carrier δ ⊆
      complexRectangleBoundary (δ.val*(a.1 : ℝ)) (δ.val*((a.1+(w : ℤ) : ℤ) : ℝ))
        (δ.val*(a.2 : ℝ)) (δ.val*((a.2+(h : ℤ) : ℤ) : ℝ)) := by
  let P := rectangleLatticePolygon a w h (by omega) (by omega)
  change P.carrier δ ⊆ _
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  have hu := (mem_rectanglePolygon_vertices_iff a w h (by omega) (by omega)
    (P.vertex i)).mp ⟨i,rfl⟩
  have hv := (mem_rectanglePolygon_vertices_iff a w h (by omega) (by omega)
    (P.vertex (i+1))).mp ⟨i+1,rfl⟩
  exact rectangle_boundary_segment_subset δ a (a.1+(w : ℤ),a.2+(h : ℤ))
    (P.vertex i) (P.vertex (i+1)) (by dsimp; omega) (by dsimp; omega)
    hu hv (P.adjacent i) hi

/-- The Jordan interior of the actual unit-step rectangle polygon is precisely
the expected open coordinate rectangle. This identifies the domain, rather
than merely proving a boundary-vertex enumeration. -/
theorem rectangleLatticePolygon_domain (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh) :
    (rectangleLatticePolygon a w h (by omega) (by omega)).domain δ =
      complexOpenRectangle (δ.val*(a.1 : ℝ)) (δ.val*((a.1+(w : ℤ) : ℤ) : ℝ))
        (δ.val*(a.2 : ℝ)) (δ.val*((a.2+(h : ℤ) : ℤ) : ℝ)) := by
  let P := rectangleLatticePolygon a w h (by omega) (by omega)
  change P.domain δ = _
  apply open_eq_rectangle_of_frontier_subset (P.domain δ)
    (P.isJordanDomain δ).isOpen (P.isJordanDomain δ).isBounded.isCompact_closure
    (P.isJordanDomain δ).isConnected.nonempty
  rw [P.frontier_domain]
  exact rectangleLatticePolygon_carrier_subset a w h hw hh δ

/-- The full closure used by the finite domain graph is the literal closed
coordinate rectangle. -/
theorem rectangleLatticePolygon_closure (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh) :
    closure ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ) =
      Complex.re ⁻¹' Icc (δ.val*(a.1 : ℝ)) (δ.val*((a.1+(w : ℤ) : ℤ) : ℝ)) ∩
        Complex.im ⁻¹' Icc (δ.val*(a.2 : ℝ)) (δ.val*((a.2+(h : ℤ) : ℤ) : ℝ)) := by
  rw [rectangleLatticePolygon_domain a w h hw hh δ]
  have hx : δ.val*(a.1 : ℝ) < δ.val*((a.1+(w : ℤ) : ℤ) : ℝ) := by
    apply mul_lt_mul_of_pos_left _ δ.property
    exact_mod_cast (show a.1 < a.1+(w : ℤ) by omega)
  have hy : δ.val*(a.2 : ℝ) < δ.val*((a.2+(h : ℤ) : ℤ) : ℝ) := by
    apply mul_lt_mul_of_pos_left _ δ.property
    exact_mod_cast (show a.2 < a.2+(h : ℤ) by omega)
  change closure (Ioo _ _ ×ℂ Ioo _ _) = Icc _ _ ×ℂ Icc _ _
  rw [Complex.closure_reProdIm,closure_Ioo hx.ne,closure_Ioo hy.ne]

/-- Exact integer bounds for the closure graph's vertex carrier. -/
theorem rectangleLatticePolygon_vertex_iff (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh) (z : FKC.LatticeVertex) :
    FKC.latticeEmbed δ z ∈
      closure ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ) ↔
      (a.1 ≤ z.1 ∧ z.1 ≤ a.1+(w : ℤ)) ∧ (a.2 ≤ z.2 ∧ z.2 ≤ a.2+(h : ℤ)) := by
  rw [rectangleLatticePolygon_closure a w h hw hh δ]
  simp only [mem_inter_iff,mem_preimage,mem_Icc,FKC.latticeEmbed_re,FKC.latticeEmbed_im,
    mul_le_mul_iff_right₀ δ.property]
  norm_cast

/-- Every nearest-neighbour bond with both endpoints in the rectangle is
an actual domain bond; no additional segment hypothesis is required. -/
theorem rectangleLatticePolygon_graph_adj_iff (a : FKC.LatticeVertex) (w h : ℕ)
    (hw : 2 ≤ w) (hh : 2 ≤ h) (δ : FKC.PositiveMesh)
    (u v : FKC.DomainVertex δ
      ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ)) :
    (FKC.domainLatticeGraph δ
      ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ)).Adj u v ↔
      FKC.squareLattice.Adj u.val v.val := by
  rw [FKC.domainLatticeGraph_adj_iff]
  constructor
  · exact And.left
  · intro huv
    refine ⟨huv,?_⟩
    have hc : Convex ℝ (closure
        ((rectangleLatticePolygon a w h (by omega) (by omega)).domain δ)) := by
      rw [rectangleLatticePolygon_closure a w h hw hh δ]
      exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
        ((convex_Icc _ _).linear_preimage Complex.imLm)
    exact hc.segment_subset u.property v.property

end PottsContinuity.PlanarTopology
