module

public import PottsContinuity.BD12.SeedWindowPinTower

/-! Independent original-input blocks and their exact disintegration into the
fixed-prefix seed kernels. All coordinates outside the block retain the given
original stream. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Jointly vary a prescribed original coordinate and its surrounding stream. -/
theorem measurable_original_stream_update_joint (c : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 c p.1) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = c
  · subst i
    convert (measurable_fst : Measurable (fun p : ℝ × (ℕ → ℝ) => p.1)) using 1
    funext p
    exact Function.update_self c p.1 p.2
  · convert ((measurable_pi_apply i).comp
      (measurable_snd : Measurable (fun p : ℝ × (ℕ → ℝ) => p.2))) using 1
    funext p
    exact Function.update_of_ne hi _ _

/-- Replace precisely the original inputs c,...,c+k-1 by independent unit
uniforms, leaving every other original input at the prescribed value. -/
def finiteOriginalPinBlock : ℕ → ℕ → (ℕ → ℝ) → Measure (ℕ → ℝ)
  | _, 0, U => Measure.dirac U
  | c, k + 1, U => finiteUnitUniform.bind (fun u =>
      finiteOriginalPinBlock (c + 1) k (Function.update U c u))

/-- The original-input block law is measurable in the full prescribed stream. -/
theorem finiteOriginalPinBlock_measurable (c k : ℕ) :
    Measurable (finiteOriginalPinBlock c k) := by
  induction k generalizing c with
  | zero => exact Measure.measurable_dirac
  | succ k ih =>
    exact Measurable.measurable_bind_right
      (f := fun (u : ℝ) (U : ℕ → ℝ) => finiteOriginalPinBlock (c + 1) k (Function.update U c u))
      ((ih (c + 1)).comp (measurable_original_stream_update_joint c))

instance finiteOriginalPinBlock_isProbabilityMeasure (c k : ℕ) (U : ℕ → ℝ) :
    IsProbabilityMeasure (finiteOriginalPinBlock c k U) := by
  induction k generalizing c U with
  | zero => dsimp [finiteOriginalPinBlock]; infer_instance
  | succ k ih =>
    let := fun u : ℝ => ih (c + 1) (Function.update U c u)
    exact probabilityKernel_bind_isProbability _ _
      ((finiteOriginalPinBlock_measurable (c + 1) k).comp (measurable_original_stream_update U c))

/-- Averaging a block of newly fixed original inputs recovers the preceding
prefix law, exactly and without restriction on the sampled seed window. -/
theorem finiteOriginalPinBlock_seedWindow_tower (c k : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ) :
    (finiteOriginalPinBlock c k U).bind
        (fun W => finiteHybridSeedWindow (c + k) W background start n) =
      finiteHybridSeedWindow c U background start n := by
  induction k generalizing c U with
  | zero =>
    simp only [finiteOriginalPinBlock, Nat.add_zero]
    exact Measure.dirac_bind (finiteHybridSeedWindow_fixedU_measurable c background start n) U
  | succ k ih =>
    have hK : Measurable (fun u : ℝ => finiteOriginalPinBlock (c + 1) k (Function.update U c u)) :=
      (finiteOriginalPinBlock_measurable (c + 1) k).comp (measurable_original_stream_update U c)
    rw [finiteOriginalPinBlock, Measure.bind_bind hK.aemeasurable
      (finiteHybridSeedWindow_fixedU_measurable (c + (k + 1)) background start n).aemeasurable]
    have hindex : c + (k + 1) = (c + 1) + k := by omega
    simp_rw [hindex, ih]
    exact finiteHybridSeedWindow_pin_tower c U background start n

end
end PottsContinuity.BD12
