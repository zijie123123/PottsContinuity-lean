module

public import PottsContinuity.Thm3.Prop4.MaximalStripSeparation
public import PottsContinuity.Thm3.Prop4.FiniteEscapeComparison
public import PottsContinuity.Thm3.Prop4.TranslatedWindowIso
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# The actual widened-strip touch bound after physical cropping

The actual maximal-root target is outside the physical crop. Every escape hits
the physical face separator. The unconditional finite comparison therefore
transfers Lemma 6's touch bound to the literal crop at every physical root.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual finite tilted touch probability is bounded by the crop's
root-to-physical-exterior event with only that exterior wired. -/
theorem maximal_strip_touch_probability_le_physical_crop (θ : Parameters)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    tiltedTouchProbability θ (4*n+4) (4*n+4) t ≤
      (measure ((squareLattice.induce (tiltedWindow (4*n+4) (4*n+4) t : Set LatticeVertex)).induce
          (maximalStripCrop n (4*n+4) (4*n+4) t z)) θ
        (BoundaryCondition.wired (Subtype.val ⁻¹'
          maximalStripSeparator n (4*n+4) (4*n+4) t z))
        (targetConnectionEvent
          ⟨tiltedWindowOrigin (4*n+4) (4*n+4) t,
            tiltedWindowOrigin_mem_maximalStripCrop n (4*n+4) (4*n+4) t z hz⟩
          (Subtype.val ⁻¹' maximalStripSeparator n (4*n+4) (4*n+4) t z))).toReal := by
  rw [tiltedTouchProbability_eq_target_measure]
  exact finite_wired_exterior_target_probability_le_crop _ θ
    (maximalStripCrop n (4*n+4) (4*n+4) t z)
    (maximalStripSeparator n (4*n+4) (4*n+4) t z)
    (tiltedWindowWiredVertices (4*n+4) (4*n+4) t 1)
    (maximalStripSeparator_subset_crop n (4*n+4) (4*n+4) t z)
    (maximalStrip_wired_target_outside_crop n t ht z hz)
    (maximalStripSeparator_is_separator n (4*n+4) (4*n+4) t z)
    ⟨_,tiltedWindowOrigin_mem_maximalStripCrop n (4*n+4) (4*n+4) t z hz⟩

/-- Lemma 6, the exact touch bound `hTouch`, supplies a polynomial physical-crop exit
bound at the explicit self-dual parameter for every real q at least one. -/
theorem maximal_strip_crop_probability_lower_of_touch (q : Set.Ici (1 : ℝ))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤
      (measure ((squareLattice.induce (tiltedWindow (4*n+4) (4*n+4) t : Set LatticeVertex)).induce
          (maximalStripCrop n (4*n+4) (4*n+4) t z)) (RSW.selfDualParameters q)
        (BoundaryCondition.wired (Subtype.val ⁻¹'
          maximalStripSeparator n (4*n+4) (4*n+4) t z))
        (targetConnectionEvent
          ⟨tiltedWindowOrigin (4*n+4) (4*n+4) t,
            tiltedWindowOrigin_mem_maximalStripCrop n (4*n+4) (4*n+4) t z hz⟩
          (Subtype.val ⁻¹' maximalStripSeparator n (4*n+4) (4*n+4) t z))).toReal := by
  exact (hTouch (4*n+4) (4*n+4) (by omega) le_rfl t ht).trans
    (maximal_strip_touch_probability_le_physical_crop (RSW.selfDualParameters q) n t ht z hz)

end
end PottsContinuity.Thm3.Prop4
