module

public import PottsContinuity.Thm3.Prop4.SafeReferenceArmTransport
public import PottsContinuity.Thm3.Prop4.TubeActualReferenceSafeExit

/-!
# Actual sampled complementary-arc probability in the primal reference fiber

The literal deleted-dual law and actual safe exit path transport to the SAME
restored primal sample. Its target is the correct complementary exterior arc.
The only hypothesis is Lemma 6, the full explicit self-dual touch bound.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance safeArmProbabilityPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance safeArmProbabilityDualEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

/-- At a safe physical central root, the actual restored primal reference
fiber has the sampled complementary-arc lower bound from Lemma 6 (touch). -/
theorem safe_reference_sampled_arm_probability_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex)
    (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (hcPhys : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (hc : if reflected then (c : ℝ) ≤ b-2*r else b+2*r ≤ (c : ℝ))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
      ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (rectangleTubeRevealedEdges n r u v) ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩).toMeasure
        {A | A.val ∪ rectangleTubeRevealedEdges n r u v ∈
          sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {(0,c)}
            (if reflected then PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
              PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True)}).toReal := by
  let R := rectangleTubeRevealedEdges n r u v
  let s := if reflected then -t else t
  let C := tubeStripPhysicalCrop n (4*n+2) (4*n+2) s c reflected
  let f := tubeStripPhysicalEmbedding n (4*n+2) (4*n+2) s c reflected
  let x : C := ⟨tiltedWindowOrigin (4*n+2) (4*n+2) s,
    tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) s c hcPhys reflected⟩
  let W : Set (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
    {z | z.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}
  let E := pathConfinedTargetEvent (tubeDeletedDualGraph n r u v) (Set.range f) W (f x)
  have hLower := tube_actual_reference_safe_exit_probability_lower_of_touch q hn r u v t b ht hu hv
    c hcPhys reflected hc hTouch
  have hprob := selfDual_frozenReferenceDualSample_probability q (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R E
  have hpre : 1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
      ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R
        ⟨R,Finset.Subset.refl _⟩).toMeasure {A | frozenReferenceDualSample _ _ _ R A ∈ E}).toReal := by
    rw [hprob]
    exact hLower
  apply hpre.trans (measureReal_mono _ (measure_ne_top _ _))
  intro A hA
  obtain ⟨y,hy,p,hD⟩ := hA
  have hx : (f x).val = (0,c) := by
    cases reflected <;> simp [f,x,tubeStripPhysicalEmbedding,tubeStripFrame,tiltedWindowOrigin]
  have hsafe : if reflected then tiltedHeight t y.val ≤ b-2*r else b+2*r ≤ tiltedHeight t y.val := by
    obtain ⟨z,hz⟩ := hD y p.end_mem_support
    have heq : y.val = tubeStripFrame c reflected z.val.val := (congrArg Subtype.val hz).symm
    have hheight := framed_tiltedWindow_safe_height (4*n+2) (4*n+2) t b r c reflected hc z.val
    simpa only [heq] using hheight
  exact restored_safe_dual_walk_gives_sampled_arm hn r hr u v huBox hvBox huX hvX t b ht hu hv
    c hcPhys reflected R A hx p hy hsafe

end
end PottsContinuity.Thm3.Prop4
