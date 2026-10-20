module

public import PottsContinuity.Thm3.RSW.InnerBoxGeometry

/-! # Actual inner and outer coordinate bounds for polygon Jordan regions -/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- A linear coordinate bound at every polygon vertex holds on every edge. -/
theorem latticePolygon_carrier_coordinate_le {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (f : ℂ →ₗ[ℝ] ℝ) (b : ℝ)
    (hvertex : ∀ i, f (FKC.latticeEmbed δ (P.vertex i)) ≤ b) :
    ∀ z ∈ P.carrier δ, f z ≤ b := by
  intro z hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact ((convex_Iic b).linear_preimage f).segment_subset
    (hvertex i) (hvertex (i+1)) hi

/-- The vertex bound controls the closure of the actual bounded Jordan region. -/
theorem latticePolygon_closure_coordinate_le {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (f : ℂ →ₗ[ℝ] ℝ) (hf : Continuous f) (ho : IsOpenMap f)
    (b : ℝ) (hvertex : ∀ i, f (FKC.latticeEmbed δ (P.vertex i)) ≤ b) :
    ∀ z ∈ closure (P.domain δ), f z ≤ b := by
  apply PlanarTopology.coordinate_le_on_closure_of_frontier (P.domain δ)
    (P.isJordanDomain δ).isOpen (P.isJordanDomain δ).isBounded.isCompact_closure f hf ho b
  intro z hz
  rw [P.frontier_domain] at hz
  exact latticePolygon_carrier_coordinate_le P δ f b hvertex z hz

/-- An open coordinate cannot reach the frontier maximum inside the polygon. -/
theorem latticePolygon_domain_coordinate_lt {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (f : ℂ →ₗ[ℝ] ℝ) (hf : Continuous f) (ho : IsOpenMap f)
    (b : ℝ) (hvertex : ∀ i, f (FKC.latticeEmbed δ (P.vertex i)) ≤ b) :
    ∀ z ∈ P.domain δ, f z < b := by
  apply PlanarTopology.coordinate_lt_on_open_of_frontier (P.domain δ)
    (P.isJordanDomain δ).isOpen (P.isJordanDomain δ).isBounded.isCompact_closure f hf ho b
  intro z hz
  rw [P.frontier_domain] at hz
  exact latticePolygon_carrier_coordinate_le P δ f b hvertex z hz

/-- The closed coordinate box is convex and hence preconnected. -/
theorem complexClosedBox_convex (c : ℤ × ℤ) (r : ℕ) :
    Convex ℝ (complexClosedBox c r) :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-- The marked unit-mesh center belongs to its actual closed coordinate box. -/
theorem latticeEmbed_center_mem_complexClosedBox (c : ℤ × ℤ) (r : ℕ) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ c ∈ complexClosedBox c r := by
  change (((c.1:ℝ)-(r:ℝ) ≤ 1*(c.1:ℝ) ∧ 1*(c.1:ℝ) ≤ (c.1:ℝ)+(r:ℝ)) ∧
    ((c.2:ℝ)-(r:ℝ) ≤ 1*(c.2:ℝ) ∧ 1*(c.2:ℝ) ≤ (c.2:ℝ)+(r:ℝ)))
  constructor <;> constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) r]

/-- Strict exclusion of the closed inner lattice box excludes the ENTIRE
continuous polygon carrier, using its nearest-neighbor edges. -/
theorem latticePolygon_carrier_disjoint_closed_inner_box {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ) (r : ℕ)
    (hout : ∀ i, (r:ℤ) < max |(P.vertex i).1-c.1| |(P.vertex i).2-c.2|) :
    Disjoint (P.carrier ⟨1,zero_lt_one⟩) (complexClosedBox c r) := by
  apply Set.disjoint_left.mpr
  intro z hz hbox
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact Set.disjoint_left.mp
    (lattice_segment_disjoint_complexClosedBox c _ _ r (P.adjacent i) (hout i) (hout (i+1))) hi hbox

/-- If the center lies in the actual polygon domain and all sampled polygon
vertices are strictly outside its radius-r box, the WHOLE closed inner box
lies in that domain. No enclosure property is inserted as an assumption. -/
theorem latticePolygon_closed_inner_box_subset_domain {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ) (r : ℕ)
    (hcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c ∈ P.domain ⟨1,zero_lt_one⟩)
    (hout : ∀ i, (r:ℤ) < max |(P.vertex i).1-c.1| |(P.vertex i).2-c.2|) :
    complexClosedBox c r ⊆ P.domain ⟨1,zero_lt_one⟩ := by
  apply PlanarTopology.subset_open_of_preconnected_frontier_disjoint
    (complexClosedBox_convex c r).isPreconnected (P.isJordanDomain _).isOpen
  · rw [P.frontier_domain]
    exact (latticePolygon_carrier_disjoint_closed_inner_box P c r hout).symm
  · exact ⟨FKC.latticeEmbed ⟨1,zero_lt_one⟩ c,
      latticeEmbed_center_mem_complexClosedBox c r,hcenter⟩

end PottsContinuity.RSW
