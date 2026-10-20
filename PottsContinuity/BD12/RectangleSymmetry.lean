module

public import PottsContinuity.BD12.DualStripOpen
public import PottsContinuity.Infinite.Symmetry
public import PottsContinuity.PD.Duality.ConnectionSymmetry

/-! Affine diagonal symmetry taking the dual strip to the primal rectangle. -/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

noncomputable section

/-- Coordinate interchange followed by the translation aligning the dual strip
with the original rectangle anchor. -/
def stripSwapIso (a : LatticeVertex) : PD.squareLattice ≃g PD.squareLattice where
  toFun z := (z.2 + a.1 - a.2 + 1, z.1 + a.2 - a.1)
  invFun z := (z.2 - a.2 + a.1, z.1 - a.1 + a.2 - 1)
  left_inv z := by ext <;> dsimp <;> omega
  right_inv z := by ext <;> dsimp <;> omega
  map_rel_iff' := by
    intro u v
    change PD.squareLattice.Adj (_, _) (_, _) ↔ PD.squareLattice.Adj u v
    simp only [squareLattice_adj_iff]
    omega

theorem stripSwapIso_mem_box (a c v : LatticeVertex) (r : ℕ) :
    stripSwapIso a v ∈ latticeBox (stripSwapIso a c) r ↔ v ∈ latticeBox c r := by
  change (v.2 + a.1 - a.2 + 1, v.1 + a.2 - a.1) ∈
    latticeBox (c.2 + a.1 - a.2 + 1, c.1 + a.2 - a.1) r ↔ _
  simp only [mem_latticeBox]
  omega

def stripSwapVertex (a : LatticeVertex) (n h : ℕ)
    (u : RectangleVertex (a.1, a.2 - 1) n (h + 1)) : RectangleVertex a (h + 1) n := by
  refine ⟨stripSwapIso a u.val, ?_⟩
  have hu := u.property
  simp only [mem_latticeRectangle, Nat.cast_add, Nat.cast_one] at hu ⊢
  change (a.1 ≤ u.val.2 + a.1 - a.2 + 1 ∧
      u.val.2 + a.1 - a.2 + 1 ≤ a.1 + ((h + 1 : ℕ) : ℤ)) ∧
    (a.2 ≤ u.val.1 + a.2 - a.1 ∧ u.val.1 + a.2 - a.1 ≤ a.2 + (n : ℤ))
  omega

def stripSwapOpenHom (a : LatticeVertex) (n h : ℕ) (ω : LatticeConfiguration) :
    (PD.rcInfiniteOpenGraph ω).induce
        (PD.FK.latticeRectangle (a.1, a.2 - 1) n (h + 1) : Set LatticeVertex) →g
      (PD.rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph (stripSwapIso a) ω)).induce
        (PD.FK.latticeRectangle a (h + 1) n : Set LatticeVertex) where
  toFun := stripSwapVertex a n h
  map_rel' := by
    intro u v huv
    change (PD.rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph (stripSwapIso a) ω)).Adj
      (stripSwapIso a u.val) (stripSwapIso a v.val)
    have hu' : (wholePlaneOpenPrimalGraph ω).Adj u.val v.val := by
      rw [wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
      exact huv
    have h := (wholePlaneOpenGraphIso (stripSwapIso a) ω).map_rel_iff'.mpr hu'
    change (wholePlaneOpenPrimalGraph
      (latticeConfigurationIsoHomeomorph (stripSwapIso a) ω)).Adj
        (stripSwapIso a u.val) (stripSwapIso a v.val) at h
    rw [wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph] at h
    exact h

/-- A vertical crossing of the strip becomes an actual horizontal crossing
after the affine lattice symmetry. -/
theorem verticalRectangle_subset_swap_horizontal (a : LatticeVertex) (n h : ℕ) :
    verticalRectangle (a.1, a.2 - 1) n (h + 1) ⊆
      latticeConfigurationIsoHomeomorph (stripSwapIso a) ⁻¹'
        horizontalRectangle a (h + 1) n := by
  rintro ω ⟨u, v, hu, hv, huv⟩
  have hp := huv.map (stripSwapOpenHom a n h ω)
  have hg := embeddedRestriction_domainGraph (PD.FK.latticeRectangle a (h + 1) n)
    (latticeConfigurationIsoHomeomorph (stripSwapIso a) ω)
  change openGraph (rectangleGraph a (h + 1) n)
    (embeddedRestriction (rectangleGraph a (h + 1) n)
      (frozenEdgeEmbedding (PD.FK.latticeRectangle a (h + 1) n))
      (latticeConfigurationIsoHomeomorph (stripSwapIso a) ω)) = _ at hg
  change ∃ x y : RectangleVertex a (h + 1) n,
    x.val ∈ rectangleLeftSide a (h + 1) n ∧
      y.val ∈ rectangleRightSide a (h + 1) n ∧ ActualConnected _ _ x y
  refine ⟨stripSwapVertex a n h u, stripSwapVertex a n h v, ?_, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨(stripSwapVertex a n h u).property, ?_⟩
    change u.val.2 + a.1 - a.2 + 1 = a.1
    dsimp at hu
    omega
  · refine Finset.mem_filter.mpr ⟨(stripSwapVertex a n h v).property, ?_⟩
    change v.val.2 + a.1 - a.2 + 1 = a.1 + ((h + 1 : ℕ) : ℤ)
    dsimp at hv
    omega
  · change (openGraph (rectangleGraph a (h + 1) n) _).Reachable _ _
    rw [hg]
    exact hp

/-- Symmetry bounds the strip crossing probability by the corresponding
horizontal rectangle probability under every frozen wired limit. -/
theorem wired_vertical_strip_le_horizontal (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (a : LatticeVertex) (n h : ℕ) :
    μ (verticalRectangle (a.1, a.2 - 1) n (h + 1)) ≤
      μ (horizontalRectangle a (h + 1) n) := by
  have hi := Infinite.wired_limit_map_latticeIso θ μ
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ)
    (stripSwapIso a) (stripSwapIso_mem_box a)
  calc
    _ ≤ μ ((latticeConfigurationIsoHomeomorph (stripSwapIso a)) ⁻¹'
      horizontalRectangle a (h + 1) n) :=
        measure_mono (verticalRectangle_subset_swap_horizontal a n h)
    _ = _ := by
      rw [← Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable _)
        (horizontalRectangle_isCylinder a (h + 1) n).measurableSet, hi]

end
end PottsContinuity.BD12
