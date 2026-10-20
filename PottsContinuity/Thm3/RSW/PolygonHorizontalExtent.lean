module

public import PottsContinuity.Thm3.RSW.PolygonBoxBounds

/-! # A genuine enclosing polygon reaches both sides of its marked center -/

@[expose] public section

namespace PottsContinuity.RSW

/-- A polygon enclosing its center has an original vertex strictly to its left. -/
theorem latticePolygon_exists_vertex_left_of_center {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ)
    (hcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c ∈ P.domain ⟨1,zero_lt_one⟩) :
    ∃ i : ZMod (m+3), (P.vertex i).1 < c.1 := by
  classical
  by_contra hn
  have hbound : ∀ i, (-Complex.reLm) (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (P.vertex i)) ≤
      -(c.1:ℝ) := by
    intro i
    have hi : c.1 ≤ (P.vertex i).1 := le_of_not_gt (fun h => hn ⟨i,h⟩)
    have hiR : (c.1:ℝ) ≤ ((P.vertex i).1:ℝ) := by exact_mod_cast hi
    change -(1*((P.vertex i).1:ℝ)) ≤ -(c.1:ℝ)
    linarith only [hiR]
  have ht := latticePolygon_domain_coordinate_lt P ⟨1,zero_lt_one⟩ (-Complex.reLm)
    Complex.continuous_re.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_re)
    (-(c.1:ℝ)) hbound _ hcenter
  change -(1*(c.1:ℝ)) < -(c.1:ℝ) at ht
  simp only [one_mul] at ht
  exact (lt_irrefl _) ht

/-- A polygon enclosing its center has an original vertex strictly to its right. -/
theorem latticePolygon_exists_vertex_right_of_center {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ)
    (hcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c ∈ P.domain ⟨1,zero_lt_one⟩) :
    ∃ i : ZMod (m+3), c.1 < (P.vertex i).1 := by
  classical
  by_contra hn
  have hbound : ∀ i, Complex.reLm (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (P.vertex i)) ≤
      (c.1:ℝ) := by
    intro i
    have hi : (P.vertex i).1 ≤ c.1 := le_of_not_gt (fun h => hn ⟨i,h⟩)
    have hiR : ((P.vertex i).1:ℝ) ≤ (c.1:ℝ) := by exact_mod_cast hi
    change 1*((P.vertex i).1:ℝ) ≤ (c.1:ℝ)
    linarith only [hiR]
  have ht := latticePolygon_domain_coordinate_lt P ⟨1,zero_lt_one⟩ Complex.reLm
    Complex.continuous_re Complex.isOpenMap_re (c.1:ℝ) hbound _ hcenter
  change 1*(c.1:ℝ) < (c.1:ℝ) at ht
  simp only [one_mul] at ht
  exact (lt_irrefl _) ht

end PottsContinuity.RSW
