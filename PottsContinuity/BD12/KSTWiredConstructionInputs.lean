module

public import PottsContinuity.BD12.RectangleHeightMonotone
public import PottsContinuity.BD12.KSTArmCoverExport
public import PottsContinuity.BD12.KSTCoverTransformOrder
public import PottsContinuity.BD12.KSTUniformWiredBridge

/-! Uniform lower bounds on the six actual wired KST construction inputs at
self-dual parameters. The shifted scales retain every arm divisibility. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- A common positive bound for the source arm and easy rectangle inputs. -/
def kstWiredInputLower : ℝ := min (kstCoverTransform (1/2)) (1/2)

theorem kstWiredInputLower_pos : 0 < kstWiredInputLower :=
  lt_min (kstCoverTransform_pos (by norm_num) (by norm_num)) (by norm_num)

theorem kstWiredInputLower_le_one : kstWiredInputLower ≤ 1 :=
  (min_le_right _ _).trans (by norm_num)

/-- Easy crossings and the exact dual-arm certificate bound all integral arms. -/
theorem wired_selfDual_kst_arm_uniform_lower (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (k : ℕ) (hk : 1 ≤ k) : kstWiredInputLower ≤ μ.real (kstArm (64*k)) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hshort := wired_selfDual_easy_rectangle_ge_half q μ hμ (-64*(k : ℤ),-512*(k : ℤ))
    (128*k) (1024*k) (by omega) (by omega)
  have hm := kstCoverTransform_strictMonoOn.monotoneOn (by norm_num : (1/2 : ℝ) ∈ Set.Icc 0 1)
    ⟨measureReal_nonneg,measureReal_le_one⟩ hshort
  exact (min_le_left _ _).trans (hm.trans (wired_kst_arm_cover_lower_bound_selfDual q μ hμ k hk))

/-- Every literal construction input is uniformly positive at scales 768*4^j. -/
theorem wired_selfDual_kst_construction_inputs_lower (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (j : ℕ) (i : Fin 6) :
    kstWiredInputLower ≤ μ.real (kstConstructionInputs (kstScale (1+j)) i) := by
  let m := kstScale (1+j)
  have hm : 1 ≤ m := kstScale_pos (1+j)
  have hp : 0 < (4 : ℕ)^j := pow_pos (by decide) j
  have heq : m = 768*4^j := by dsimp only [m,kstScale]; rw [pow_add]; norm_num; ring
  have hArm : kstWiredInputLower ≤ μ.real (kstArm m) := by
    have h := wired_selfDual_kst_arm_uniform_lower q μ hμ (12*4^j) (by omega)
    have hm' : m = 64*(12*4^j) := by rw [heq]; ring
    simpa only [hm'] using h
  have hArm' : kstWiredInputLower ≤ μ.real (kstArm (5*m/2)) := by
    have h := wired_selfDual_kst_arm_uniform_lower q μ hμ (30*4^j) (by omega)
    have hm' : 5*m/2 = 64*(30*4^j) := by rw [heq]; omega
    simpa only [hm'] using h
  fin_cases i
  · change kstWiredInputLower ≤ μ.real (kstTranslateEvent _ (kstArm m))
    rw [wired_kstTranslateEvent_probability _ μ hμ _ (kstArm_isOpen m).measurableSet]
    exact hArm
  · change kstWiredInputLower ≤ μ.real (kstTranslateEvent _ (kstArm m))
    rw [wired_kstTranslateEvent_probability _ μ hμ _ (kstArm_isOpen m).measurableSet]
    exact hArm
  · change kstWiredInputLower ≤ μ.real (kstTranslateEvent _ (kstArm (5*m/2)))
    rw [wired_kstTranslateEvent_probability _ μ hμ _ (kstArm_isOpen (5*m/2)).measurableSet]
    exact hArm'
  · change kstWiredInputLower ≤ μ.real (kstTranslateEvent _ (kstArm (5*m/2)))
    rw [wired_kstTranslateEvent_probability _ μ hμ _ (kstArm_isOpen (5*m/2)).measurableSet]
    exact hArm'
  · change kstWiredInputLower ≤ μ.real (horizontalRectangle _ (31*m/4) (8*m))
    exact (min_le_right _ _).trans (wired_selfDual_easy_rectangle_ge_half q μ hμ _ _ _ (by omega) (by omega))
  · change kstWiredInputLower ≤ μ.real (horizontalRectangle _ (31*m/4) (8*m))
    exact (min_le_right _ _).trans (wired_selfDual_easy_rectangle_ge_half q μ hμ _ _ _ (by omega) (by omega))

end
end PottsContinuity.BD12
