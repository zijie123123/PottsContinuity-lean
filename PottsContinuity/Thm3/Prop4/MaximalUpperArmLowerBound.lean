module

public import PottsContinuity.Thm3.Prop4.MaximalStripRestoredArm
public import PottsContinuity.Thm3.Prop4.SupportingLineArmTarget
public import PottsContinuity.Thm3.Prop4.UpperExcursionBoundaryRoot

/-!
# Upper complementary sampled arm at every actual maximal root

A root in the original square either has its own sampled star port or is
the upper-right corner handled by its genuine adjacent top port. Every
boundary-root and length-zero case is retained in the same probability bound.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance maximalUpperArmEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Every actual revealed state has the corrected upper-star-port arm lower
bound, from touch and the deterministic supporting-line reveal geometry. -/
theorem maximal_upper_star_arm_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (u v z : LatticeVertex)
    (huB : u ∈ box n) (hvB : v ∈ box n) (hzB : z ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (hoff : 0 < tubeLineOffset u v z)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hu : tiltedHeight t u ≤ tiltedHeight t z) (hv : tiltedHeight t v ≤ tiltedHeight t z)
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (B : RemovedConfiguration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) R)
    (hR : ∀ e ∈ R,
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source ≤ tiltedHeight t z ∧
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target ≤ tiltedHeight t z)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤
      ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R B).toMeasure
        {A | A.val ∪ B.val ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
            ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩)
          (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
          (fun _ => True)}).toReal := by
  let a : LatticeVertex := (-(n : ℤ),-(n : ℤ))
  let zr : RectangleVertex a (2*n) (2*n) :=
    ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩
  let E := sampledRectangleDualArmEvent a (2*n) (2*n)
    (sampledStarFacePorts a (2*n) (2*n) zr)
    (PlanarTopology.rectangleUpperDualArc a (2*n) (2*n) u v) (fun _ => True)
  change _ ≤ ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R B).toMeasure
    {A | A.val ∪ B.val ∈ E}).toReal
  by_cases hcorner : z = ((n : ℤ),(n : ℤ))
  · have hAll : {A : RemainingConfiguration (rectangleGraph a (2*n) (2*n)) R |
        A.val ∪ B.val ∈ E} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro A
      exact upperRight_corner_sampled_upper_arm hn zr hcorner u v (A.val ∪ B.val)
    rw [hAll,measure_univ,ENNReal.toReal_one]
    have hk : (1 : ℝ) ≤ ((4*n+4 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 4*n+4 by omega)
    have hk2 : (1 : ℝ) ≤ ((4*n+4 : ℕ) : ℝ)^2 := one_le_pow₀ hk
    have hden : (1 : ℝ) ≤ 20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hk2) hk2
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr hden
  · have hz : z ∈ rectangleDualExpanded a (2*n) (2*n) := by
      have hb := hzB
      simp only [box,Finset.mem_product,Finset.mem_Icc] at hb
      rw [rectangleDualExpanded,mem_latticeRectangle]
      dsimp [a]
      omega
    have hLower := maximal_restored_arm_lower_of_touch q n t ht z hz R B hR hTouch
    apply hLower.trans (measureReal_mono ?_ (measure_ne_top _ _))
    intro A hA
    have hu' : (u.2 : ℝ) ≤ t*u.1+tiltedHeight t z := by dsimp [tiltedHeight] at hu ⊢; linarith only [hu]
    have hv' : (v.2 : ℝ) ≤ t*v.1+tiltedHeight t z := by dsimp [tiltedHeight] at hv ⊢; linarith only [hv]
    have hTarget := supporting_line_sampled_arm_target n t (tiltedHeight t z) u v z
      huB hvB huX hvX hu' hv'
      (upper_excursion_boundary_root_upper_arc hn u v z huX hvX hzB hcorner hoff) hA
    obtain ⟨f,hf,s,hs,p,_⟩ := hTarget
    refine ⟨f,?_,s,hs,p,fun _ _ => True.intro⟩
    have hfz : f = z := hf
    rw [hfz]
    exact box_vertex_sampled_star_port n ⟨z,hzB⟩ hcorner

end
end PottsContinuity.Thm3.Prop4
