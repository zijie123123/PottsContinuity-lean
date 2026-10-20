module

public import PottsContinuity.Thm3.Prop4.TubeReferenceSafeExit
public import PottsContinuity.Thm3.Prop4.DeletedReferenceFirstExit

/-!
# The safe-exit lower bound in the genuine sampled reference law

Stop the ambient path at its first physical exterior face and use the exact
marginal on genuine retained dual bonds. The same explicit touch lower bound
therefore holds on the true sampled dual graph, with safe path confinement.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The true sampled dual graph with the entire crossed tube reveal deleted. -/
abbrev tubeDeletedDualGraph (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    SimpleGraph (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
  edgeRestriction (rectangleDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v))

/-- The actual sampled safe-exit lower bound requires only Lemma 6 (touch);
all ambient caps have been removed by the proved first-exit map and marginal. -/
theorem tube_actual_reference_safe_exit_probability_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (u v : LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (hcPhys : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (hc : if reflected then (c : ℝ) ≤ b-2*r else b+2*r ≤ (c : ℝ))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    let s := if reflected then -t else t;
    let C := tubeStripPhysicalCrop n (4*n+2) (4*n+2) s c reflected;
    let f := tubeStripPhysicalEmbedding n (4*n+2) (4*n+2) s c reflected;
    let x : C := ⟨tiltedWindowOrigin (4*n+2) (4*n+2) s,
      tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) s c hcPhys reflected⟩;
    let W : Set (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
      {z | z.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)};
    1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
      (measure (tubeDeletedDualGraph n r u v) (RSW.selfDualParameters q)
        (rectangleDualBoundaryCondition (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (pathConfinedTargetEvent (tubeDeletedDualGraph n r u v) (Set.range f) W (f x))).toReal := by
  have hLower := tube_reference_safe_exit_probability_lower_of_touch q hn r u v t b ht hu hv
    c hcPhys reflected hc hTouch
  dsimp only at hLower ⊢
  exact hLower.trans (rectangle_deleted_ambient_confined_exit_probability_le_actual
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v)
    (RSW.selfDualParameters q) _ _)

end
end PottsContinuity.Thm3.Prop4
