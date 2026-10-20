module

public import PottsContinuity.Thm3.Push.IntervalArmConnectionRestoration
public import PottsContinuity.Thm3.Push.RestoredConditionalLaw

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 PottsContinuity.Exploration MeasureTheory
noncomputable section
local instance armRecordLowerEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- On EVERY actual successful joint arm record, the original source
intervals connect with the uniform mixed-square lower bound. Records already
joining the sources are included, and every original boundary is retained. -/
theorem intervalArmPair_record_connection_lower_bound
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂) (ξ : BoundaryCondition (RectangleVertex (0,0) N N))
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂) :
    1 / (1 + (q : ℝ)^2) ≤
      (((law (rectangleGraph (0,0) N N) (criticalParameters q) ξ).filter
        (revealRecordEvent (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂) A)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent _
            (intervalArmJointFilledReveal_stable N l₁ r₁ l₂ r₂) A]
          exact frozenStateEvent_support (criticalParameters q) ξ _ (revealRecordConfiguration _ A))).toMeasure
        (arcsConnectionEvent (rectangleGraph (0,0) N N)
          (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))).toReal := by
  let G := rectangleGraph (0,0) N N
  let r := intervalArmJointFilledReveal N l₁ r₁ l₂ r₂
  let F := revealRecordConfiguration r A
  let T := arcsConnectionEvent G (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)
  let μ := (law G (criticalParameters q) ξ).filter (frozenStateEvent (r A) F)
    (frozenStateEvent_support (criticalParameters q) ξ (r A) F)
  let ρ := (law G (criticalParameters q) ξ).filter (revealRecordEvent r A)
    (by
      rw [revealRecordEvent_eq_frozenStateEvent r (intervalArmJointFilledReveal_stable N l₁ r₁ l₂ r₂) A]
      exact frozenStateEvent_support (criticalParameters q) ξ (r A) F)
  have hμρ : μ=ρ := by
    dsimp only [μ,ρ]
    congr 1
    exact (revealRecordEvent_eq_frozenStateEvent r (intervalArmJointFilledReveal_stable N l₁ r₁ l₂ r₂) A).symm
  change 1/(1+(q : ℝ)^2) ≤ (ρ.toMeasure T).toReal
  rw [← hμρ]
  by_cases hjoined : A ∩ r A ∈ T
  · have hsupport : ∀ B ∈ μ.support, B ∈ T := by
      intro B hB
      have hstates := (PMF.mem_support_filter_iff _).mp hB |>.1
      change B ∩ r A=A ∩ r A at hstates
      apply arcsConnectionEvent_isUpperSet _ _ _ hjoined
      rw [← hstates]
      exact Finset.inter_subset_left
    have hprob : μ.toMeasure T=μ.toMeasure Set.univ := by
      apply PMF.toMeasure_apply_eq_of_inter_support_eq _
        MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
      ext B
      constructor
      · rintro ⟨_,hB⟩
        exact ⟨Set.mem_univ _,hB⟩
      · rintro ⟨_,hB⟩
        exact ⟨hsupport B hB,hB⟩
    rw [hprob,measure_univ,ENNReal.toReal_one]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<1+(q : ℝ)^2)).mpr
    nlinarith [sq_nonneg (q : ℝ)]
  · let E := {C : Configuration (edgeRestriction G (r A)) |
      embeddedConfigurationRestriction (activeUnexaminedGraph G (r A)) (edgeRestriction G (r A))
        (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le_edgeRestriction G (r A)) C ∈
        arcsConnectionEvent _ (twoRevealActiveLeftArc G (intervalArmFilledLeftReveal N l₁ r₁ A)
          (intervalArmFilledRightReveal N l₂ r₂ A))
          (twoRevealActiveRightArc G (intervalArmFilledLeftReveal N l₁ r₁ A)
            (intervalArmFilledRightReveal N l₂ r₂ A))}
    have hbound : 1/(1+(q : ℝ)^2) ≤
        (measure (edgeRestriction G (r A)) (criticalParameters q) (frozenBoundary ξ F.val) E).toReal :=
      intervalArmJoint_remaining_attachment_lower_bound q N hN l₁ r₁ l₂ r₂
        hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hjoined ξ
    have hfull := edgeRestrictionLaw_map_restore_eq_filter G (criticalParameters q) ξ (r A) F
    have hprob := congrArg (fun ρ : PMF (Configuration G) => ρ.toMeasure T) hfull
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hprob
    calc
      1/(1+(q : ℝ)^2) ≤
          (measure (edgeRestriction G (r A)) (criticalParameters q) (frozenBoundary ξ F.val) E).toReal := hbound
      _ ≤ ((law (edgeRestriction G (r A)) (criticalParameters q) (frozenBoundary ξ F.val)).toMeasure
          ((restoreRemainingConfiguration G (r A) F) ⁻¹' T)).toReal := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro C hC
        exact intervalArmJoint_remaining_connection_restores_sources N l₁ r₁ l₂ r₂
          hl₁ h₁ hr₁ hl₂ h₂ hr₂ A hA C hC
      _ = (μ.toMeasure T).toReal := congrArg ENNReal.toReal hprob

end
end PottsContinuity.Push
