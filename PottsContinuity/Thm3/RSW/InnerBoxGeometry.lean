module

public import PottsContinuity.Thm3.RSW.PolygonVertexIntersection

/-! # Unit lattice edges outside a closed inner box stay outside it -/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- The actual closed coordinate box in the unit-mesh complex plane. -/
def complexClosedBox (c : ℤ × ℤ) (r : ℕ) : Set ℂ :=
  Complex.re ⁻¹' Icc ((c.1:ℝ)-(r:ℝ)) ((c.1:ℝ)+(r:ℝ)) ∩
    Complex.im ⁻¹' Icc ((c.2:ℝ)-(r:ℝ)) ((c.2:ℝ)+(r:ℝ))

/-- A nearest-neighbor edge with both endpoints outside the closed lattice
box lies in one of its four strict exterior coordinate half-planes. -/
theorem lattice_edge_outside_box_common_side (c u v : ℤ × ℤ) (r : ℕ)
    (hadj : FKC.squareLattice.Adj u v)
    (hu : (r:ℤ) < max |u.1-c.1| |u.2-c.2|)
    (hv : (r:ℤ) < max |v.1-c.1| |v.2-c.2|) :
    (u.1 < c.1-(r:ℤ) ∧ v.1 < c.1-(r:ℤ)) ∨
    (c.1+(r:ℤ) < u.1 ∧ c.1+(r:ℤ) < v.1) ∨
    (u.2 < c.2-(r:ℤ) ∧ v.2 < c.2-(r:ℤ)) ∨
    (c.2+(r:ℤ) < u.2 ∧ c.2+(r:ℤ) < v.2) := by
  have hr : (0:ℤ) ≤ r := Nat.cast_nonneg r
  rw [FKC.squareLattice_adj_iff] at hadj
  simp only [abs_eq_max_neg] at hu hv
  rcases hadj with h | h <;> omega

/-- Thus the entire Euclidean unit segment, not only its endpoints, avoids
the closed inner box. -/
theorem lattice_segment_disjoint_complexClosedBox (c u v : ℤ × ℤ) (r : ℕ)
    (hadj : FKC.squareLattice.Adj u v)
    (hu : (r:ℤ) < max |u.1-c.1| |u.2-c.2|)
    (hv : (r:ℤ) < max |v.1-c.1| |v.2-c.2|) :
    Disjoint (segment ℝ (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u)
      (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v)) (complexClosedBox c r) := by
  apply Set.disjoint_left.mpr
  intro z hz hbox
  change (((c.1:ℝ)-(r:ℝ) ≤ z.re ∧ z.re ≤ (c.1:ℝ)+(r:ℝ)) ∧
    ((c.2:ℝ)-(r:ℝ) ≤ z.im ∧ z.im ≤ (c.2:ℝ)+(r:ℝ))) at hbox
  rcases lattice_edge_outside_box_common_side c u v r hadj hu hv with h | h | h | h
  · have hu' : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).re < (c.1:ℝ)-(r:ℝ) := by
      simp only [FKC.latticeEmbed_re,one_mul]
      exact_mod_cast h.1
    have hv' : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).re < (c.1:ℝ)-(r:ℝ) := by
      simp only [FKC.latticeEmbed_re,one_mul]
      exact_mod_cast h.2
    have hz' : z.re < (c.1:ℝ)-(r:ℝ) :=
      ((convex_Iio ((c.1:ℝ)-(r:ℝ))).linear_preimage Complex.reLm).segment_subset hu' hv' hz
    exact (not_lt_of_ge hbox.1.1) hz'
  · have hu' : (c.1:ℝ)+(r:ℝ) < (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).re := by
      simp only [FKC.latticeEmbed_re,one_mul]
      exact_mod_cast h.1
    have hv' : (c.1:ℝ)+(r:ℝ) < (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).re := by
      simp only [FKC.latticeEmbed_re,one_mul]
      exact_mod_cast h.2
    have hz' : (c.1:ℝ)+(r:ℝ) < z.re :=
      ((convex_Ioi ((c.1:ℝ)+(r:ℝ))).linear_preimage Complex.reLm).segment_subset hu' hv' hz
    exact (not_lt_of_ge hbox.1.2) hz'
  · have hu' : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).im < (c.2:ℝ)-(r:ℝ) := by
      simp only [FKC.latticeEmbed_im,one_mul]
      exact_mod_cast h.1
    have hv' : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).im < (c.2:ℝ)-(r:ℝ) := by
      simp only [FKC.latticeEmbed_im,one_mul]
      exact_mod_cast h.2
    have hz' : z.im < (c.2:ℝ)-(r:ℝ) :=
      ((convex_Iio ((c.2:ℝ)-(r:ℝ))).linear_preimage Complex.imLm).segment_subset hu' hv' hz
    exact (not_lt_of_ge hbox.2.1) hz'
  · have hu' : (c.2:ℝ)+(r:ℝ) < (FKC.latticeEmbed ⟨1,zero_lt_one⟩ u).im := by
      simp only [FKC.latticeEmbed_im,one_mul]
      exact_mod_cast h.1
    have hv' : (c.2:ℝ)+(r:ℝ) < (FKC.latticeEmbed ⟨1,zero_lt_one⟩ v).im := by
      simp only [FKC.latticeEmbed_im,one_mul]
      exact_mod_cast h.2
    have hz' : (c.2:ℝ)+(r:ℝ) < z.im :=
      ((convex_Ioi ((c.2:ℝ)+(r:ℝ))).linear_preimage Complex.imLm).segment_subset hu' hv' hz
    exact (not_lt_of_ge hbox.2.2) hz'

end PottsContinuity.RSW
