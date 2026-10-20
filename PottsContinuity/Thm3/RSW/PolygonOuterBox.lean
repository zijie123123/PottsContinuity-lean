module

public import PottsContinuity.Thm3.RSW.PolygonBoxBounds

/-! # The closed outer box contains the actual polygon-domain closure -/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- Literal lattice coordinate bounds embed into the corresponding continuous
closed coordinate box at unit mesh. -/
theorem latticeEmbed_mem_complexClosedBox (c v : ℤ × ℤ) (R : ℕ)
    (hv : max |v.1-c.1| |v.2-c.2| ≤ (R:ℤ)) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ v ∈ complexClosedBox c R := by
  have hx := (le_max_left |v.1-c.1| |v.2-c.2|).trans hv
  have hy := (le_max_right |v.1-c.1| |v.2-c.2|).trans hv
  rw [abs_le] at hx hy
  have hx₁ : c.1-(R:ℤ) ≤ v.1 := by omega
  have hx₂ : v.1 ≤ c.1+(R:ℤ) := by omega
  have hy₁ : c.2-(R:ℤ) ≤ v.2 := by omega
  have hy₂ : v.2 ≤ c.2+(R:ℤ) := by omega
  change (((c.1:ℝ)-(R:ℝ) ≤ 1*(v.1:ℝ) ∧ 1*(v.1:ℝ) ≤ (c.1:ℝ)+(R:ℝ)) ∧
    ((c.2:ℝ)-(R:ℝ) ≤ 1*(v.2:ℝ) ∧ 1*(v.2:ℝ) ≤ (c.2:ℝ)+(R:ℝ)))
  simp only [one_mul]
  exact ⟨⟨by exact_mod_cast hx₁,by exact_mod_cast hx₂⟩,
    ⟨by exact_mod_cast hy₁,by exact_mod_cast hy₂⟩⟩

/-- Bounds on every original polygon vertex bound the closure of its genuine
bounded Jordan interior, not only its geometric boundary. -/
theorem latticePolygon_closure_subset_outer_box {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ) (R : ℕ)
    (hvertex : ∀ i, max |(P.vertex i).1-c.1| |(P.vertex i).2-c.2| ≤ (R:ℤ)) :
    closure (P.domain ⟨1,zero_lt_one⟩) ⊆ complexClosedBox c R := by
  have hv : ∀ i, FKC.latticeEmbed ⟨1,zero_lt_one⟩ (P.vertex i) ∈ complexClosedBox c R :=
    fun i => latticeEmbed_mem_complexClosedBox c (P.vertex i) R (hvertex i)
  have hxplus := latticePolygon_closure_coordinate_le P ⟨1,zero_lt_one⟩ Complex.reLm
    Complex.continuous_re Complex.isOpenMap_re ((c.1:ℝ)+(R:ℝ)) (fun i => (hv i).1.2)
  have hyplus := latticePolygon_closure_coordinate_le P ⟨1,zero_lt_one⟩ Complex.imLm
    Complex.continuous_im Complex.isOpenMap_im ((c.2:ℝ)+(R:ℝ)) (fun i => (hv i).2.2)
  have hxmin := latticePolygon_closure_coordinate_le P ⟨1,zero_lt_one⟩ (-Complex.reLm)
    Complex.continuous_re.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_re)
    (-((c.1:ℝ)-(R:ℝ))) (fun i => neg_le_neg (hv i).1.1)
  have hymin := latticePolygon_closure_coordinate_le P ⟨1,zero_lt_one⟩ (-Complex.imLm)
    Complex.continuous_im.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_im)
    (-((c.2:ℝ)-(R:ℝ))) (fun i => neg_le_neg (hv i).2.1)
  intro z hz
  exact ⟨⟨neg_le_neg_iff.mp (hxmin z hz),hxplus z hz⟩,
    ⟨neg_le_neg_iff.mp (hymin z hz),hyplus z hz⟩⟩

end PottsContinuity.RSW
