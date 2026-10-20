module

public import PottsContinuity.Thm3.Prop4.TubeStripPhysicalSeparation
public import PottsContinuity.Thm3.Prop4.FiniteEscapeComparison
public import PottsContinuity.Thm3.Prop4.TranslatedWindowIso
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# The actual widened-strip touch bound after physical cropping

The wired target is genuinely outside the physical crop. Every escape hits
the physical face separator. The unconditional finite comparison therefore
transfers Lemma 6's touch bound to the literal crop in either orientation.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual finite tilted touch probability is bounded by the crop's
root-to-physical-exterior event with only that exterior wired. -/
theorem widened_tilted_touch_probability_le_physical_crop (θ : Parameters)
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (c : ℤ) (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool) :
    tiltedTouchProbability θ (4*n+2) (4*n+2) t ≤
      (measure ((squareLattice.induce (tiltedWindow (4*n+2) (4*n+2) t : Set LatticeVertex)).induce
          (tubeStripPhysicalCrop n (4*n+2) (4*n+2) t c reflected)) θ
        (BoundaryCondition.wired (Subtype.val ⁻¹'
          tubeStripPhysicalSeparator n (4*n+2) (4*n+2) t c reflected))
        (targetConnectionEvent
          ⟨tiltedWindowOrigin (4*n+2) (4*n+2) t,
            tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) t c hc reflected⟩
          (Subtype.val ⁻¹' tubeStripPhysicalSeparator n (4*n+2) (4*n+2) t c reflected))).toReal := by
  rw [tiltedTouchProbability_eq_target_measure]
  exact finite_wired_exterior_target_probability_le_crop _ θ
    (tubeStripPhysicalCrop n (4*n+2) (4*n+2) t c reflected)
    (tubeStripPhysicalSeparator n (4*n+2) (4*n+2) t c reflected)
    (tiltedWindowWiredVertices (4*n+2) (4*n+2) t 1)
    (tubeStripPhysicalSeparator_subset_crop n (4*n+2) (4*n+2) t c reflected)
    (widened_tilted_wired_target_outside_physicalCrop hn t ht c hc reflected)
    (tubeStripPhysicalSeparator_is_separator n (4*n+2) (4*n+2) t c reflected)
    ⟨_,tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) t c hc reflected⟩

/-- Lemma 6, the exact touch bound `hTouch`, supplies a polynomial physical-crop exit
bound at the explicit self-dual parameter for every real q at least one. -/
theorem widened_physical_crop_probability_lower_of_touch (q : Set.Ici (1 : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (c : ℤ) (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) ≤
      (measure ((squareLattice.induce (tiltedWindow (4*n+2) (4*n+2) t : Set LatticeVertex)).induce
          (tubeStripPhysicalCrop n (4*n+2) (4*n+2) t c reflected)) (RSW.selfDualParameters q)
        (BoundaryCondition.wired (Subtype.val ⁻¹'
          tubeStripPhysicalSeparator n (4*n+2) (4*n+2) t c reflected))
        (targetConnectionEvent
          ⟨tiltedWindowOrigin (4*n+2) (4*n+2) t,
            tiltedWindowOrigin_mem_physicalCrop n (4*n+2) (4*n+2) t c hc reflected⟩
          (Subtype.val ⁻¹' tubeStripPhysicalSeparator n (4*n+2) (4*n+2) t c reflected))).toReal := by
  exact (hTouch (4*n+2) (4*n+2) (by omega) le_rfl t ht).trans
    (widened_tilted_touch_probability_le_physical_crop (RSW.selfDualParameters q) hn t ht c hc reflected)

end
end PottsContinuity.Thm3.Prop4
