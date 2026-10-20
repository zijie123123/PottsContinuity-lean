module

public import PottsContinuity.Thm3.Prop4.TubeSafeExteriorArcs

/-!
# Exact complementary-arc selection above a supporting line

Both adjacent face labels are used. At the left exterior side the interior
face supplies the inequality at the actual original boundary coordinate.
This retains the unit-cell offset without a strict slope restriction.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial

private theorem supporting_line_above_bottom (n : ℕ) (t b x : ℝ)
    (hL : -(n : ℝ) ≤ t*(-(n : ℝ))+b) (hR : -(n : ℝ) ≤ t*(n : ℝ)+b)
    (hx : -(n : ℝ) ≤ x ∧ x ≤ n) : -(n : ℝ) ≤ t*x+b := by
  by_cases ht : 0 ≤ t
  · have hm := mul_le_mul_of_nonneg_left hx.1 ht
    linarith only [hL,hm]
  · have hm := mul_le_mul_of_nonpos_left hx.2 (le_of_lt (lt_of_not_ge ht))
    linarith only [hR,hm]

/-- An exterior face of a genuine sampled bond whose two face labels are
above a line supported above the marks is on their actual upper arc. -/
theorem supporting_line_sampled_exterior_face_upper_arc (n : ℕ) (t b : ℝ)
    (u v : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (hu : (u.2 : ℝ) ≤ t*u.1+b) (hv : (v.2 : ℝ) ≤ t*v.1+b)
    (e : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (s : LatticeVertex) (hs : s = e.val.faceBase false ∨ s = e.val.faceBase true)
    (hb : s ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (h0 : b ≤ tiltedHeight t (e.val.faceBase false))
    (h1 : b ≤ tiltedHeight t (e.val.faceBase true)) :
    s ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
  have huY : -(n : ℤ) ≤ u.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp huB).2).1
  have hvY : -(n : ℤ) ≤ v.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hvB).2).1
  have huYR : -(n : ℝ) ≤ (u.2 : ℝ) := by exact_mod_cast huY
  have hvYR : -(n : ℝ) ≤ (v.2 : ℝ) := by exact_mod_cast hvY
  rw [huX] at hu
  rw [hvX] at hv
  push_cast at hu hv
  have hL : -(n : ℝ) ≤ t*(-(n : ℝ))+b := huYR.trans hu
  have hR : -(n : ℝ) ≤ t*(n : ℝ)+b := hvYR.trans hv
  have hnot := (Finset.mem_filter.mp hb).2
  have hinside : ¬ (-(n : ℤ) ≤ s.1 ∧ s.1 < n ∧ -(n : ℤ) ≤ s.2 ∧ s.2 < n) := by
    intro h
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hb).1,?_⟩
    dsimp
    omega
  have he0 := (mem_latticeRectangle _ _ _ _).mp e.property.1
  have he1 := (mem_latticeRectangle _ _ _ _).mp e.property.2
  rcases e with ⟨⟨⟨x,y⟩,axis⟩,he⟩
  cases axis <;> rcases hs with rfl | rfl
  all_goals
    simp only [LatticeBond.source,LatticeBond.target,LatticeBond.faceBase,tiltedHeight,
      ] at he0 he1 hinside h0 h1 ⊢
    push_cast at he0 he1 h0 h1
  · have hy : y = -(n : ℤ) := by omega
    have hx : -(n : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ n := by exact_mod_cast (show -(n : ℤ) ≤ x ∧ x ≤ n by omega)
    have hline := supporting_line_above_bottom n t b x hL hR hx
    rw [hy] at h0
    push_cast at h0
    linarith only [h0,hline]
  · have hy : y = (n : ℤ) := by omega
    apply Or.inl
    dsimp
    exact ⟨by omega,by omega,by omega⟩
  · have hx : x = -(n : ℤ) := by omega
    have hy : u.2 ≤ y := by
      rw [hx] at h1
      push_cast at h1
      exact_mod_cast (show (u.2 : ℝ) ≤ y by linarith only [hu,h1])
    apply Or.inr ∘ Or.inl
    dsimp
    exact ⟨by omega,by omega,hy,by omega⟩
  · have hx : x = (n : ℤ) := by omega
    have hy : v.2 ≤ y := by
      rw [hx] at h1
      push_cast at h1
      exact_mod_cast (show (v.2 : ℝ) ≤ y by linarith only [hv,h1])
    apply Or.inr ∘ Or.inr
    dsimp
    exact ⟨by omega,by omega,hy,by omega⟩

end PottsContinuity.Thm3.Prop4
