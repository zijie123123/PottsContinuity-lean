module

public import PottsContinuity.Thm3.Prop4.ConfinedTargetComparison
public import PottsContinuity.Thm3.Prop4.TubeStripDeletedEmbedding
public import PottsContinuity.Thm3.Prop4.WidenedStripCropComparison

/-!
# The actual reference safe-exit bound from the explicit touch bound

The physical crop has a proved lower exit probability and a proved embedding
in the exact deleted ambient reference. Finite FK comparison retains a path
in the embedded safe crop. The touching estimate of Lemma 6 is the hypothesis
`hTouch`; it is proved by
`Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal` with
`RSW.selfDual_tiltedStrip_reflected_marginal`, combined in `Thm4Plane.FinalRootRoutes`.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual expanded induced dual graph with every crossed revealed tube
bond deleted, retaining the entire physical face carrier. -/
abbrev tubeDeletedAmbientGraph (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    SimpleGraph (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
  edgeRestriction (rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (rectangleAmbientCrossedReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (rectangleTubeRevealedEdges n r u v))

/-- The safely framed actual reference exit event has the explicit polynomial
lower bound, conditional only on the all-slope touching estimate `hTouch`. -/
theorem tube_reference_safe_exit_probability_lower_of_touch (q : Set.Ici (1 : ℝ))
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
      (measure (tubeDeletedAmbientGraph n r u v) (RSW.selfDualParameters q)
        (rectangleDualBoundaryCondition (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (pathConfinedTargetEvent (tubeDeletedAmbientGraph n r u v) (Set.range f) W (f x))).toReal := by
  dsimp only
  let s := if reflected then -t else t
  let C := tubeStripPhysicalCrop n (4*n+2) (4*n+2) s c reflected
  let f := tubeStripPhysicalEmbedding n (4*n+2) (4*n+2) s c reflected
  let G := (squareLattice.induce (tiltedWindow (4*n+2) (4*n+2) s : Set LatticeVertex)).induce C
  let x : C := ⟨tiltedWindowOrigin (4*n+2) (4*n+2) s,
    tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) s c hcPhys reflected⟩
  let W : Set (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
    {z | z.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}
  have hts : s ∈ Set.Icc (-1 : ℝ) 1 := by
    have habs := abs_le.mp ht
    dsimp [s]
    cases reflected <;> dsimp <;> constructor <;> linarith only [habs.1,habs.2]
  have hmap : G.map f ≤ tubeDeletedAmbientGraph n r u v :=
    tubeStripPhysicalEmbedding_map_le_deleted n (4*n+2) (4*n+2) r u v t b ht hu hv c reflected hc
  have hcompare := embedded_wired_confined_target_probability_le G (tubeDeletedAmbientGraph n r u v)
    f hmap (RSW.selfDualParameters q) W x
  have hpre : f ⁻¹' W = Subtype.val ⁻¹' tubeStripPhysicalSeparator n (4*n+2) (4*n+2) s c reflected := rfl
  rw [hpre] at hcompare
  exact (widened_physical_crop_probability_lower_of_touch q hn s hts c hcPhys reflected hTouch).trans hcompare

end
end PottsContinuity.Thm3.Prop4
