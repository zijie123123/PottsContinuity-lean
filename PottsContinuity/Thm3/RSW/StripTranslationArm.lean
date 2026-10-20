module

public import PottsContinuity.Thm3.RSW.StripHorizontalTranslation

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- Translating the original sampled arm preserves its entire height band. -/
theorem stripBandArm_translated_mem (n : ℕ) (H a b c : ℤ)
    (ω : StripConfiguration n) (hω : ω ∈ stripBandArm n H a b) :
    stripHorizontalTranslationConfiguration n c ω ∈ stripBandArm n H (a+c) (b+c) := by
  obtain ⟨u,v,p,ha,hb,hu,hv,hp⟩ := hω
  let φ := stripHorizontalTranslationOpenHom n c ω
  refine ⟨φ u,φ v,p.map φ,?_,?_,hu,hv,?_⟩
  · change a+c ≤ u.val.1+c
    omega
  · change u.val.1+c ≤ b+c
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact hp w hw

/-- The translated band arm has exactly the original sampled preimage. -/
theorem stripBandArm_translation_iff (n : ℕ) (H a b c : ℤ)
    (ω : StripConfiguration n) :
    stripHorizontalTranslationConfiguration n c ω ∈ stripBandArm n H (a+c) (b+c) ↔
      ω ∈ stripBandArm n H a b := by
  constructor
  · intro h
    have ht := stripBandArm_translated_mem n H (a+c) (b+c) (-c)
      (stripHorizontalTranslationConfiguration n c ω) h
    rw [stripHorizontalTranslationConfiguration_neg_cancel n c ω] at ht
    simpa only [add_neg_cancel_right] using ht
  · exact stripBandArm_translated_mem n H a b c ω

/-- Whole-law translation invariance transports the corrected source arm;
the equality is derived for this actual height-confined sampled event. -/
theorem stripBandArm_real_translation_of_translationInvariant
    (n : ℕ) (H a b c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : μ.map (stripHorizontalTranslationConfiguration n c) = μ) :
    μ.real (stripBandArm n H (a+c) (b+c)) = μ.real (stripBandArm n H a b) := by
  have hpre : (stripHorizontalTranslationConfiguration n c) ⁻¹'
      stripBandArm n H (a+c) (b+c) = stripBandArm n H a b := by
    ext ω
    exact stripBandArm_translation_iff n H a b c ω
  calc
    _ = (μ.map (stripHorizontalTranslationConfiguration n c)).real
        (stripBandArm n H (a+c) (b+c)) := by rw [hμ]
    _ = μ.real ((stripHorizontalTranslationConfiguration n c) ⁻¹'
        stripBandArm n H (a+c) (b+c)) := by
      unfold Measure.real
      rw [Measure.map_apply (stripHorizontalTranslationConfiguration n c).continuous.measurable
        (stripBandArm_measurableSet n H (a+c) (b+c))]
    _ = _ := by rw [hpre]

end PottsContinuity.RSW
