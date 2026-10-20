-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeEdges.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.LatticeEmbedding
public import Mathlib.Analysis.Convex.Segment

/-!
# Euclidean intersections of square-lattice unit edges

An embedded lattice vertex on a nearest-neighbor edge is an endpoint.
Two distinct unordered nearest-neighbor edges meet only at shared endpoints.
The distinction of unordered edges is essential: reversing an edge gives the
same entire segment, not a new edge with only endpoint intersections.
-/

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

private theorem segment_coordinate_parameter (δ : PositiveMesh)
    {u v : LatticeVertex} {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.re / δ.val = (1 - t) * (u.1 : ℝ) + t * (v.1 : ℝ) ∧
      z.im / δ.val = (1 - t) * (u.2 : ℝ) + t * (v.2 : ℝ) := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hz
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · apply (div_eq_iff δ.property.ne').mpr
    have hre := congrArg Complex.re htz
    simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, latticeEmbed_re] at hre
    nlinarith only [hre]
  · apply (div_eq_iff δ.property.ne').mpr
    have him := congrArg Complex.im htz
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, latticeEmbed_im] at him
    nlinarith only [him]

private theorem horizontal_segment_coordinates (δ : PositiveMesh) (a b : ℤ) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a + 1, b))) :
    (a : ℝ) ≤ z.re / δ.val ∧ z.re / δ.val ≤ (a : ℝ) + 1 ∧
      z.im / δ.val = (b : ℝ) := by
  obtain ⟨t, ht0, ht1, hre, him⟩ := segment_coordinate_parameter δ hz
  simp only [Int.cast_add, Int.cast_one] at hre him
  constructor
  · nlinarith only [hre, ht0]
  constructor
  · nlinarith only [hre, ht1]
  · nlinarith only [him]

private theorem vertical_segment_coordinates (δ : PositiveMesh) (a b : ℤ) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a, b + 1))) :
    z.re / δ.val = (a : ℝ) ∧ (b : ℝ) ≤ z.im / δ.val ∧
      z.im / δ.val ≤ (b : ℝ) + 1 := by
  obtain ⟨t, ht0, ht1, hre, him⟩ := segment_coordinate_parameter δ hz
  simp only [Int.cast_add, Int.cast_one] at hre him
  constructor
  · nlinarith only [hre]
  constructor
  · nlinarith only [him, ht0]
  · nlinarith only [him, ht1]

private theorem eq_latticeEmbed_of_coordinates (δ : PositiveMesh) (z : ℂ) (a b : ℤ)
    (hre : z.re / δ.val = (a : ℝ)) (him : z.im / δ.val = (b : ℝ)) :
    z = latticeEmbed δ (a, b) := by
  apply Complex.ext
  · exact ((div_eq_iff δ.property.ne').mp hre).trans (mul_comm _ _)
  · exact ((div_eq_iff δ.property.ne').mp him).trans (mul_comm _ _)

private theorem adjacent_unordered_edge_cases {u v : LatticeVertex}
    (h : squareLattice.Adj u v) :
    (∃ a b : ℤ, s(u, v) = s((a, b), (a + 1, b))) ∨
      (∃ a b : ℤ, s(u, v) = s((a, b), (a, b + 1))) := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  change ((a + 1 = c ∨ c + 1 = a) ∧ b = d) ∨
    (a = c ∧ (b + 1 = d ∨ d + 1 = b)) at h
  rcases h with ⟨h | h, rfl⟩ | ⟨rfl, h | h⟩
  · subst c
    exact Or.inl ⟨a, b, rfl⟩
  · subst a
    exact Or.inl ⟨c, b, Sym2.eq_swap⟩
  · subst d
    exact Or.inr ⟨a, b, rfl⟩
  · subst b
    exact Or.inr ⟨a, d, Sym2.eq_swap⟩

private theorem lattice_segment_eq_of_sym2_eq (δ : PositiveMesh)
    {u v x y : LatticeVertex} (h : s(u, v) = s(x, y)) :
    segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) =
      segment ℝ (latticeEmbed δ x) (latticeEmbed δ y) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

private theorem endpoint_iff_of_sym2_eq (δ : PositiveMesh)
    {u v x y : LatticeVertex} (h : s(u, v) = s(x, y)) (z : ℂ) :
    (z = latticeEmbed δ u ∨ z = latticeEmbed δ v) ↔
      (z = latticeEmbed δ x ∨ z = latticeEmbed δ y) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact or_comm

private theorem lattice_vertex_horizontal_segment (δ : PositiveMesh) (a b : ℤ)
    (x : LatticeVertex)
    (hx : latticeEmbed δ x ∈
      segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a + 1, b))) :
    x = (a, b) ∨ x = (a + 1, b) := by
  have h := horizontal_segment_coordinates δ a b hx
  simp only [latticeEmbed_re, latticeEmbed_im, mul_div_cancel_left₀ _ δ.property.ne'] at h
  have hleft : a ≤ x.1 := by exact_mod_cast h.1
  have hright : x.1 ≤ a + 1 := by exact_mod_cast h.2.1
  have hy : x.2 = b := by exact_mod_cast h.2.2
  have hx : x.1 = a ∨ x.1 = a + 1 := by omega
  exact hx.elim (fun h => Or.inl (Prod.ext h hy)) (fun h => Or.inr (Prod.ext h hy))

private theorem lattice_vertex_vertical_segment (δ : PositiveMesh) (a b : ℤ)
    (x : LatticeVertex)
    (hx : latticeEmbed δ x ∈
      segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a, b + 1))) :
    x = (a, b) ∨ x = (a, b + 1) := by
  have h := vertical_segment_coordinates δ a b hx
  simp only [latticeEmbed_re, latticeEmbed_im, mul_div_cancel_left₀ _ δ.property.ne'] at h
  have hx : x.1 = a := by exact_mod_cast h.1
  have hleft : b ≤ x.2 := by exact_mod_cast h.2.1
  have hright : x.2 ≤ b + 1 := by exact_mod_cast h.2.2
  have hy : x.2 = b ∨ x.2 = b + 1 := by omega
  exact hy.elim (fun h => Or.inl (Prod.ext hx h)) (fun h => Or.inr (Prod.ext hx h))

/-- A unit nearest-neighbor edge contains no lattice vertex other than its endpoints. -/
theorem latticeEmbed_mem_segment_iff (δ : PositiveMesh) {u v x : LatticeVertex}
    (huv : squareLattice.Adj u v) :
    latticeEmbed δ x ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ↔
      x = u ∨ x = v := by
  constructor
  · intro hx
    have he : latticeEmbed δ x = latticeEmbed δ u ∨ latticeEmbed δ x = latticeEmbed δ v := by
      rcases adjacent_unordered_edge_cases huv with ⟨a, b, h⟩ | ⟨a, b, h⟩
      · rw [lattice_segment_eq_of_sym2_eq δ h] at hx
        apply (endpoint_iff_of_sym2_eq δ h _).mpr
        rcases lattice_vertex_horizontal_segment δ a b x hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rw [lattice_segment_eq_of_sym2_eq δ h] at hx
        apply (endpoint_iff_of_sym2_eq δ h _).mpr
        rcases lattice_vertex_vertical_segment δ a b x hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    exact he.elim (fun h => Or.inl (latticeEmbed_injective δ h))
      (fun h => Or.inr (latticeEmbed_injective δ h))
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

private theorem integer_unit_interval_overlap {a c : ℤ} {r : ℝ}
    (ha0 : (a : ℝ) ≤ r) (ha1 : r ≤ (a : ℝ) + 1)
    (hc0 : (c : ℝ) ≤ r) (hc1 : r ≤ (c : ℝ) + 1) (hne : a ≠ c) :
    r = (a : ℝ) ∨ r = (a : ℝ) + 1 := by
  rcases lt_or_gt_of_ne hne with hac | hca
  · have hi : a + 1 ≤ c := by omega
    have hr : (a : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hi
    exact Or.inr (le_antisymm ha1 (hr.trans hc0))
  · have hi : c + 1 ≤ a := by omega
    have hr : (c : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hi
    exact Or.inl (le_antisymm (hc1.trans hr) ha0)

private theorem horizontal_horizontal_intersection (δ : PositiveMesh) (a b c d : ℤ)
    (hne : s((a, b), (a + 1, b)) ≠ s((c, d), (c + 1, d))) {z : ℂ}
    (h1 : z ∈ segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a + 1, b)))
    (h2 : z ∈ segment ℝ (latticeEmbed δ (c, d)) (latticeEmbed δ (c + 1, d))) :
    ∃ w : LatticeVertex, z = latticeEmbed δ w := by
  have hfirst := horizontal_segment_coordinates δ a b h1
  have hsecond := horizontal_segment_coordinates δ c d h2
  have hbd : b = d := by exact_mod_cast hfirst.2.2.symm.trans hsecond.2.2
  have hac : a ≠ c := by
    intro hac
    subst c
    subst d
    exact hne rfl
  rcases integer_unit_interval_overlap hfirst.1 hfirst.2.1 hsecond.1 hsecond.2.1 hac with h | h
  · exact ⟨(a, b), eq_latticeEmbed_of_coordinates δ z a b h hfirst.2.2⟩
  · refine ⟨(a + 1, b), eq_latticeEmbed_of_coordinates δ z (a + 1) b ?_ hfirst.2.2⟩
    simpa only [Int.cast_add, Int.cast_one] using h

private theorem vertical_vertical_intersection (δ : PositiveMesh) (a b c d : ℤ)
    (hne : s((a, b), (a, b + 1)) ≠ s((c, d), (c, d + 1))) {z : ℂ}
    (h1 : z ∈ segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a, b + 1)))
    (h2 : z ∈ segment ℝ (latticeEmbed δ (c, d)) (latticeEmbed δ (c, d + 1))) :
    ∃ w : LatticeVertex, z = latticeEmbed δ w := by
  have hfirst := vertical_segment_coordinates δ a b h1
  have hsecond := vertical_segment_coordinates δ c d h2
  have hac : a = c := by exact_mod_cast hfirst.1.symm.trans hsecond.1
  have hbd : b ≠ d := by
    intro hbd
    subst c
    subst d
    exact hne rfl
  rcases integer_unit_interval_overlap hfirst.2.1 hfirst.2.2 hsecond.2.1 hsecond.2.2 hbd with h | h
  · exact ⟨(a, b), eq_latticeEmbed_of_coordinates δ z a b hfirst.1 h⟩
  · refine ⟨(a, b + 1), eq_latticeEmbed_of_coordinates δ z a (b + 1) hfirst.1 ?_⟩
    simpa only [Int.cast_add, Int.cast_one] using h

private theorem horizontal_vertical_intersection (δ : PositiveMesh) (a b c d : ℤ) {z : ℂ}
    (h1 : z ∈ segment ℝ (latticeEmbed δ (a, b)) (latticeEmbed δ (a + 1, b)))
    (h2 : z ∈ segment ℝ (latticeEmbed δ (c, d)) (latticeEmbed δ (c, d + 1))) :
    ∃ w : LatticeVertex, z = latticeEmbed δ w := by
  exact ⟨(c, b), eq_latticeEmbed_of_coordinates δ z c b
    (vertical_segment_coordinates δ c d h2).1
    (horizontal_segment_coordinates δ a b h1).2.2⟩

private theorem lattice_intersection_is_lattice (δ : PositiveMesh)
    {u v x y : LatticeVertex} (huv : squareLattice.Adj u v) (hxy : squareLattice.Adj x y)
    (hne : s(u, v) ≠ s(x, y)) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ∩
      segment ℝ (latticeEmbed δ x) (latticeEmbed δ y)) :
    ∃ w : LatticeVertex, z = latticeEmbed δ w := by
  obtain ⟨h1, h2⟩ := hz
  rcases adjacent_unordered_edge_cases huv with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · rw [lattice_segment_eq_of_sym2_eq δ hab] at h1
    rcases adjacent_unordered_edge_cases hxy with ⟨c, d, hcd⟩ | ⟨c, d, hcd⟩
    · rw [lattice_segment_eq_of_sym2_eq δ hcd] at h2
      apply horizontal_horizontal_intersection δ a b c d _ h1 h2
      intro heq
      exact hne (hab.trans (heq.trans hcd.symm))
    · rw [lattice_segment_eq_of_sym2_eq δ hcd] at h2
      exact horizontal_vertical_intersection δ a b c d h1 h2
  · rw [lattice_segment_eq_of_sym2_eq δ hab] at h1
    rcases adjacent_unordered_edge_cases hxy with ⟨c, d, hcd⟩ | ⟨c, d, hcd⟩
    · rw [lattice_segment_eq_of_sym2_eq δ hcd] at h2
      exact horizontal_vertical_intersection δ c d a b h2 h1
    · rw [lattice_segment_eq_of_sym2_eq δ hcd] at h2
      apply vertical_vertical_intersection δ a b c d _ h1 h2
      intro heq
      exact hne (hab.trans (heq.trans hcd.symm))

/-- Distinct unordered unit lattice edges intersect only at endpoints shared
by both edges. No geometric nonintersection hypothesis is imposed. -/
theorem mem_inter_lattice_segments_endpoints (δ : PositiveMesh)
    {u v x y : LatticeVertex} (huv : squareLattice.Adj u v) (hxy : squareLattice.Adj x y)
    (hne : s(u, v) ≠ s(x, y)) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ∩
      segment ℝ (latticeEmbed δ x) (latticeEmbed δ y)) :
    (z = latticeEmbed δ u ∨ z = latticeEmbed δ v) ∧
      (z = latticeEmbed δ x ∨ z = latticeEmbed δ y) := by
  obtain ⟨w, rfl⟩ := lattice_intersection_is_lattice δ huv hxy hne hz
  constructor
  · rcases (latticeEmbed_mem_segment_iff δ huv).mp hz.1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rcases (latticeEmbed_mem_segment_iff δ hxy).mp hz.2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end

end PottsContinuity.FKC
