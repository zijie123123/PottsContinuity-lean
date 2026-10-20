module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.DirectSideAverage

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open MeasureTheory PD.FK Thm4Plane
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

theorem slitScreenSideFactor_of_uniform_residual_bounds
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (hbound : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)),
        c ≤ slitRightResidualCrossingProbability ⟨q,hq⟩ m A ∧
        c ≤ slitLeftResidualCrossingProbability ⟨q,hq⟩ m A) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₂^2 * (slitScreenFiniteMeasure ⟨q,hq⟩ m).real (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q,hq⟩ m).real
          (slitScreenEvent m ∩
            (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
              FKC.FiniteFK.slitScreenRightCrossingEvent m)) := by
  obtain ⟨c,hc,hb⟩ := hbound
  refine ⟨c,hc,?_⟩
  intro m hm
  have hr := slitScreen_right_factor_of_residual_bounds ⟨q,hq⟩ m c
    (fun A _ => (hb m hm A).1)
  have hl := slitScreen_left_factor_of_residual_bounds ⟨q,hq⟩ m hm c
    (fun A _ => (hb m hm A).2)
  calc
    c^2 * (slitScreenFiniteMeasure ⟨q,hq⟩ m).real (slitScreenEvent m) =
      c * (c * (slitScreenFiniteMeasure ⟨q,hq⟩ m).real (slitScreenEvent m)) := by ring
    _ ≤ c * (slitScreenFiniteMeasure ⟨q,hq⟩ m).real
        (slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) :=
      mul_le_mul_of_nonneg_left hr hc.le
    _ ≤ _ := hl

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
