module

public import PottsContinuity.Thm3.Prop4.MaximalRootStarPorts

/-!
# Zero-length exits of the actual upper-excursion root

Inside the original square the physical dual boundary consists only of the
top and right face layers. The unused upper-right corner is treated by its
proved adjacent sampled star port instead.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- A noncorner original upper-excursion vertex on the physical dual boundary
already lies on the correct upper complementary arc. -/
theorem upper_excursion_boundary_root_upper_arc {n : ℕ} (hn : 1 ≤ n)
    (u v z : LatticeVertex) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (hzB : z ∈ box n) (hz : z ≠ ((n : ℤ),(n : ℤ)))
    (hoff : 0 < tubeLineOffset u v z)
    (hboundary : z ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    z ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
  have hb := hzB
  simp only [box,Finset.mem_product,Finset.mem_Icc] at hb
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hnot := (Finset.mem_filter.mp hboundary).2
  have hside : z.1 = (n : ℤ) ∨ z.2 = (n : ℤ) := by
    by_contra h
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hboundary).1,?_⟩
    dsimp
    omega
  rcases hside with hx | hy
  · have hy : z.2 < n := by
      by_contra h
      apply hz
      exact Prod.ext hx (by omega)
    have hyv : v.2 ≤ z.2 := by
      dsimp [tubeLineOffset] at hoff
      rw [huX,hvX,hx] at hoff
      by_contra h
      have hmul := mul_nonneg (show (0 : ℤ) ≤ 2*n by omega) (show 0 ≤ v.2-z.2 by omega)
      nlinarith only [hoff,hmul]
    apply Or.inr ∘ Or.inr
    dsimp
    exact ⟨by omega,by omega,hyv,by omega⟩
  · have hx : z.1 < n := by
      by_contra h
      apply hz
      exact Prod.ext (by omega) hy
    apply Or.inl
    dsimp
    exact ⟨by omega,by omega,by omega⟩

end PottsContinuity.Thm3.Prop4
