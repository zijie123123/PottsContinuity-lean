module

public import PottsContinuity.BD12.InfiniteRadiusEvent
public import PottsContinuity.BD12.BoxOneArmTranslation
public import PottsContinuity.BD12.KSTHypotheses

/-! Literal translation of shell events and their wired infinite-volume probabilities. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section

/-- Translation preserves actual radius-shell connection events. -/
theorem infiniteRadiusEvent_translation (a c : LatticeVertex) (n : ℕ) (ω : LatticeConfiguration) :
    edgeTranslate a ω ∈ infiniteRadiusEvent (latticeTranslate a c) n ↔ ω ∈ infiniteRadiusEvent c n := by
  constructor
  · rintro ⟨v,hv,hconn⟩
    obtain ⟨z,rfl⟩ := (latticeTranslationIso a).surjective v
    exact ⟨z, (latticeRadius_translate a c z).symm.trans hv,
      (openGraphTranslationIso a ω).reachable_iff.mp hconn⟩
  · rintro ⟨v,hv,hconn⟩
    exact ⟨latticeTranslate a v, (latticeRadius_translate a c v).trans hv,
      (openGraphTranslationIso a ω).reachable_iff.mpr hconn⟩

/-- Wired shell probabilities are preserved by simultaneous translation. -/
theorem wired_infiniteRadiusEvent_probability_translation (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (a c : LatticeVertex) (n : ℕ) :
    μ.real (infiniteRadiusEvent (latticeTranslate a c) n) = μ.real (infiniteRadiusEvent c n) := by
  have hevent : latticeConfigurationTranslate a ⁻¹' infiniteRadiusEvent (latticeTranslate a c) n =
      infiniteRadiusEvent c n := Set.ext (infiniteRadiusEvent_translation a c n)
  have h := congrArg (fun ν : Measure LatticeConfiguration => ν (infiniteRadiusEvent (latticeTranslate a c) n))
    (wired_translation_invariant θ μ hμ a)
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable a)
    (infiniteRadiusEvent_isCylinder (latticeTranslate a c) n).measurableSet, hevent] at h
  exact congrArg ENNReal.toReal h.symm

/-- Every centred shell has the same wired probability as the origin shell. -/
theorem wired_infiniteRadiusEvent_probability_eq_origin (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (c : LatticeVertex) (n : ℕ) :
    μ.real (infiniteRadiusEvent c n) = μ.real (infiniteRadiusEvent (0,0) n) := by
  have hc : latticeTranslate c (0,0) = c := by ext <;> simp [latticeTranslate]
  simpa only [hc] using wired_infiniteRadiusEvent_probability_translation θ μ hμ c (0,0) n

end
end PottsContinuity.BD12
