-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCells.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.PolygonDomain
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Actual open square-lattice cells and their Jordan side

The cell based at an integer vertex is the genuine open coordinate square of
side length `δ`. Every nearest-neighbor lattice segment lies on integer grid
lines and misses every open cell. Consequently a lattice polygon also misses
the entire open cell. Convexity and the proved Jordan separation theorem then
put that entire cell on one side, detectable by its actual center.

No claim that adjacent cells lie on opposite sides is assumed here.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge

noncomputable section

/-- The open mesh square whose lower-left corner is `latticeEmbed δ c`. -/
def openLatticeCell (δ : PositiveMesh) (c : LatticeVertex) : Set ℂ :=
  Complex.re ⁻¹' Ioo (δ.val * (c.1 : ℝ)) (δ.val * ((c.1 : ℝ) + 1)) ∩
    Complex.im ⁻¹' Ioo (δ.val * (c.2 : ℝ)) (δ.val * ((c.2 : ℝ) + 1))

/-- The actual Euclidean center of the mesh square. -/
def latticeCellCenter (δ : PositiveMesh) (c : LatticeVertex) : ℂ :=
  ⟨δ.val * ((c.1 : ℝ) + 1 / 2), δ.val * ((c.2 : ℝ) + 1 / 2)⟩

theorem mem_openLatticeCell_iff (δ : PositiveMesh) (c : LatticeVertex) (z : ℂ) :
    z ∈ openLatticeCell δ c ↔
      (δ.val * (c.1 : ℝ) < z.re ∧ z.re < δ.val * ((c.1 : ℝ) + 1)) ∧
      (δ.val * (c.2 : ℝ) < z.im ∧ z.im < δ.val * ((c.2 : ℝ) + 1)) := Iff.rfl

theorem latticeCellCenter_mem (δ : PositiveMesh) (c : LatticeVertex) :
    latticeCellCenter δ c ∈ openLatticeCell δ c := by
  change (δ.val * (c.1 : ℝ) < δ.val * ((c.1 : ℝ) + 1 / 2) ∧
    δ.val * ((c.1 : ℝ) + 1 / 2) < δ.val * ((c.1 : ℝ) + 1)) ∧
    (δ.val * (c.2 : ℝ) < δ.val * ((c.2 : ℝ) + 1 / 2) ∧
    δ.val * ((c.2 : ℝ) + 1 / 2) < δ.val * ((c.2 : ℝ) + 1))
  constructor <;> constructor <;> nlinarith [δ.property]

theorem openLatticeCell_nonempty (δ : PositiveMesh) (c : LatticeVertex) :
    (openLatticeCell δ c).Nonempty := ⟨latticeCellCenter δ c, latticeCellCenter_mem δ c⟩

theorem convex_openLatticeCell (δ : PositiveMesh) (c : LatticeVertex) :
    Convex ℝ (openLatticeCell δ c) :=
  ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem isConnected_openLatticeCell (δ : PositiveMesh) (c : LatticeVertex) :
    IsConnected (openLatticeCell δ c) :=
  (convex_openLatticeCell δ c).isConnected (openLatticeCell_nonempty δ c)

private theorem not_between_mesh_integers (δ : PositiveMesh) (a k : ℤ) :
    ¬(δ.val * (a : ℝ) < δ.val * (k : ℝ) ∧
      δ.val * (k : ℝ) < δ.val * ((a : ℝ) + 1)) := by
  rintro ⟨hlo, hhi⟩
  have hlo' : (a : ℝ) < (k : ℝ) := (mul_lt_mul_iff_right₀ δ.property).mp hlo
  have hhi' : (k : ℝ) < (a : ℝ) + 1 := (mul_lt_mul_iff_right₀ δ.property).mp hhi
  have ha : a < k := by exact_mod_cast hlo'
  have hk : k < a + 1 := by exact_mod_cast hhi'
  omega

/-- Every actual unit lattice segment lies on a horizontal or vertical integer
grid line, including its entire closed segment. -/
theorem lattice_segment_on_grid_line (δ : PositiveMesh) {u v : LatticeVertex}
    (huv : squareLattice.Adj u v) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v)) :
    (∃ k : ℤ, z.re = δ.val * (k : ℝ)) ∨ (∃ k : ℤ, z.im = δ.val * (k : ℝ)) := by
  rcases huv with ⟨_, hy⟩ | ⟨hx, _⟩
  · right
    refine ⟨u.2, ?_⟩
    have hc := (convex_singleton (𝕜 := ℝ) (δ.val * (u.2 : ℝ))).linear_preimage
      Complex.imLm
    apply hc.segment_subset (x := latticeEmbed δ u) (y := latticeEmbed δ v) ?_ ?_ hz
    · simp [latticeEmbed]
    · simp [latticeEmbed, ← hy]
  · left
    refine ⟨u.1, ?_⟩
    have hc := (convex_singleton (𝕜 := ℝ) (δ.val * (u.1 : ℝ))).linear_preimage
      Complex.reLm
    apply hc.segment_subset (x := latticeEmbed δ u) (y := latticeEmbed δ v) ?_ ?_ hz
    · simp [latticeEmbed]
    · simp [latticeEmbed, ← hx]

/-- No open unit cell intersects any nearest-neighbor lattice segment. -/
theorem openLatticeCell_disjoint_lattice_segment (δ : PositiveMesh) (c : LatticeVertex)
    {u v : LatticeVertex} (huv : squareLattice.Adj u v) :
    Disjoint (openLatticeCell δ c) (segment ℝ (latticeEmbed δ u) (latticeEmbed δ v)) := by
  rw [Set.disjoint_left]
  intro z hz hs
  rw [mem_openLatticeCell_iff] at hz
  rcases lattice_segment_on_grid_line δ huv hs with ⟨k, hk⟩ | ⟨k, hk⟩
  · apply not_between_mesh_integers δ c.1 k
    simpa only [← hk] using hz.1
  · apply not_between_mesh_integers δ c.2 k
    simpa only [← hk] using hz.2

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- The actual unbounded Jordan region in the existing complex coordinate chart. -/
def exterior (δ : PositiveMesh) : Set ℂ :=
  complexPlaneCoordinates ⁻¹' Schoenflies.outside (complexPlaneCoordinates '' P.carrier δ)

theorem exterior_eq_compl_closure_domain (δ : PositiveMesh) :
    P.exterior δ = (closure (P.domain δ))ᶜ := by
  rw [P.closure_domain]
  ext z
  have himg : complexPlaneCoordinates z ∈ complexPlaneCoordinates '' P.carrier δ ↔
      z ∈ P.carrier δ := complexPlaneCoordinates.injective.mem_set_image
  change (complexPlaneCoordinates z ∉ complexPlaneCoordinates '' P.carrier δ ∧
      ¬Bornology.IsBounded (connectedComponentIn
        (complexPlaneCoordinates '' P.carrier δ)ᶜ (complexPlaneCoordinates z))) ↔
    ¬(z ∈ P.domain δ ∨ z ∈ P.carrier δ)
  simp only [domain, complexInside, mem_preimage, Schoenflies.mem_inside_iff, himg]
  tauto

theorem disjoint_domain_exterior (δ : PositiveMesh) :
    Disjoint (P.domain δ) (P.exterior δ) := by
  rw [P.exterior_eq_compl_closure_domain]
  exact disjoint_compl_right.mono_left subset_closure

theorem openLatticeCell_disjoint_carrier (δ : PositiveMesh) (c : LatticeVertex) :
    Disjoint (openLatticeCell δ c) (P.carrier δ) := by
  rw [Set.disjoint_left]
  intro z hz hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact Set.disjoint_left.mp (openLatticeCell_disjoint_lattice_segment δ c (P.adjacent i)) hz hi

/-- A whole genuine open cell lies in one actual Jordan complementary region. -/
theorem openLatticeCell_subset_domain_or_exterior (δ : PositiveMesh) (c : LatticeVertex) :
    openLatticeCell δ c ⊆ P.domain δ ∨ openLatticeCell δ c ⊆ P.exterior δ := by
  let C := complexPlaneCoordinates '' P.carrier δ
  let S := complexPlaneCoordinates '' openLatticeCell δ c
  have hs : IsPreconnected S := (isConnected_openLatticeCell δ c).isPreconnected.image
    complexPlaneCoordinates complexPlaneCoordinates.continuous.continuousOn
  have hc : complexPlaneCoordinates (latticeCellCenter δ c) ∈ S :=
    mem_image_of_mem _ (latticeCellCenter_mem δ c)
  have hSC : S ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
    have hwz := complexPlaneCoordinates.injective he
    subst w
    exact Set.disjoint_left.mp (P.openLatticeCell_disjoint_carrier δ c) hz hw
  have hsub := hs.subset_connectedComponentIn hc hSC
  rcases (P.isSeparating_carrier δ).isRegionOf_connectedComponentIn (hSC hc) with hi | he
  · left
    intro z hz
    change complexPlaneCoordinates z ∈ Schoenflies.inside C
    rw [← hi]
    exact hsub (mem_image_of_mem _ hz)
  · right
    intro z hz
    change complexPlaneCoordinates z ∈ Schoenflies.outside C
    rw [← he]
    exact hsub (mem_image_of_mem _ hz)

theorem openLatticeCell_subset_domain_iff_center (δ : PositiveMesh) (c : LatticeVertex) :
    openLatticeCell δ c ⊆ P.domain δ ↔ latticeCellCenter δ c ∈ P.domain δ := by
  constructor
  · exact fun h => h (latticeCellCenter_mem δ c)
  · intro hc
    rcases P.openLatticeCell_subset_domain_or_exterior δ c with h | h
    · exact h
    · exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hc
        (h (latticeCellCenter_mem δ c))).elim

/-- Membership in the actual Jordan interior is constant throughout an open cell. -/
theorem openLatticeCell_mem_domain_iff_center (δ : PositiveMesh) (c : LatticeVertex)
    {z : ℂ} (hz : z ∈ openLatticeCell δ c) :
    z ∈ P.domain δ ↔ latticeCellCenter δ c ∈ P.domain δ := by
  constructor
  · intro hzD
    rcases P.openLatticeCell_subset_domain_or_exterior δ c with h | h
    · exact h (latticeCellCenter_mem δ c)
    · exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ) hzD (h hz)).elim
  · intro hc
    exact (P.openLatticeCell_subset_domain_iff_center δ c).mpr hc hz

end LatticePolygon
end

end PottsContinuity.FKC
