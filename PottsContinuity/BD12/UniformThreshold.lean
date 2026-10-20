module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Tactic

/-! The literal uniform-threshold realization of a Boolean probability,
including both endpoints. -/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory Set
noncomputable section

/-- The Lebesgue probability law on the closed unit interval. -/
def finiteUnitUniform : Measure ℝ := volume.restrict (Icc 0 1)

instance finiteUnitUniform_isProbabilityMeasure : IsProbabilityMeasure finiteUnitUniform := by
  constructor
  simp [finiteUnitUniform, Real.volume_Icc]

/-- DRT's threshold convention: open if u is at least the closed probability. -/
def finiteUniformBit (p u : ℝ) : Bool := if 1 - p ≤ u then true else false

theorem finiteUniformBit_measurable (p : ℝ) : Measurable (finiteUniformBit p) := by
  apply measurable_to_bool
  have h : finiteUniformBit p ⁻¹' {true} = Ici (1 - p) := by
    ext u
    simp [finiteUniformBit]
  rw [h]
  exact measurableSet_Ici

theorem finiteUnitUniform_threshold_true (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finiteUnitUniform (finiteUniformBit p ⁻¹' {true}) = ENNReal.ofReal p := by
  have hpre : finiteUniformBit p ⁻¹' {true} = Ici (1 - p) := by
    ext u
    simp [finiteUniformBit]
  rw [hpre, finiteUnitUniform, Measure.restrict_apply measurableSet_Ici]
  have hi : Ici (1 - p) ∩ Icc (0 : ℝ) 1 = Icc (1 - p) 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hu, _, hu1⟩
      exact ⟨hu, hu1⟩
    · rintro ⟨hu, hu1⟩
      exact ⟨hu, by linarith, hu1⟩
  rw [hi, Real.volume_Icc]
  congr 1
  ring

theorem finiteUnitUniform_threshold_false (p : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    finiteUnitUniform (finiteUniformBit p ⁻¹' {false}) = ENNReal.ofReal (1 - p) := by
  have hpre : finiteUniformBit p ⁻¹' {false} = Iio (1 - p) := by
    ext u
    simp [finiteUniformBit, not_le]
    constructor <;> intro h <;> linarith
  rw [hpre, finiteUnitUniform, Measure.restrict_apply measurableSet_Iio]
  have hi : Iio (1 - p) ∩ Icc (0 : ℝ) 1 = Ico 0 (1 - p) := by
    ext u
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨hu, hu0, _⟩
      exact ⟨hu0, hu⟩
    · rintro ⟨hu0, hu⟩
      exact ⟨hu, hu0, by linarith⟩
  rw [hi, Real.volume_Ico, sub_zero]

end
end PottsContinuity.BD12
