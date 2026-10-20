module

public import PottsContinuity.BD12.FixedOriginalHybridLaw
public import PottsContinuity.BD12.OriginalPinBlockTower
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Observable moments transferred between the actual finite replacement product
space and the fully fixed-original seed kernel, followed by actual block towers. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Joint real observable moments of X and a finite family of actual hybrids. -/
theorem finiteFixedHybridFamily_product_integral
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U V : ℕ → ℝ) (cutoff : ι → ℕ) (background : ℕ → ℝ × ℝ)
    (T : FiniteRevealTree E ∅) (g : Finset E × (ι → Finset E) → ℝ) :
    (∫ v, g (finiteOriginalEval w U T ∅,
      fun j => finiteJointHybridEval w f (cutoff j) U
        (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) =
      ∫ S, g (finiteHybridFamilyEval w f cutoff T ∅ (fun _ => ∅) false S)
        ∂finiteHybridSeedWindow (Fintype.card E) U background 0 (Fintype.card E) := by
  have hm : Measurable (fun v : Fin (Fintype.card E) → ℝ => (finiteOriginalEval w U T ∅,
      fun j => finiteJointHybridEval w f (cutoff j) U
        (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)) := by
    apply Measurable.prodMk measurable_const
    apply measurable_pi_iff.mpr
    intro j
    exact (finiteJointHybridEval_measurable w f (cutoff j) T ∅ ∅ false).comp
      (measurable_const.prodMk (finiteSeedExtension_measurable _ V))
  rw [← integral_map_of_stronglyMeasurable hm (measurable_of_finite g).stronglyMeasurable,
    finiteFixedHybridFamily_product_eq_seedWindow,
    integral_map_of_stronglyMeasurable
      (finiteHybridFamilyEval_measurable w f cutoff T ∅ (fun _ => ∅) false)
      (measurable_of_finite g).stronglyMeasurable]

/-- Arbitrary real observable moments of one actual fixed-U hybrid. -/
theorem finiteJointHybridEval_product_integral
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (cutoff : ℕ) (U V : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    (T : FiniteRevealTree E ∅) :
    (∫ v, g (finiteJointHybridEval w f cutoff U (finiteSeedExtension (Fintype.card E) V v)
      T ∅ ∅ false) ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) =
      ∫ S, g (finiteJointHybridEval w f cutoff (fun i => (S i).1) (fun i => (S i).2)
        T ∅ ∅ false) ∂finiteHybridSeedWindow (Fintype.card E) U background 0 (Fintype.card E) := by
  have h := finiteFixedHybridFamily_product_integral w f U V (fun _ : Unit => cutoff)
    background T (fun XY => g (XY.2 ()))
  simpa only [finiteHybridFamilyEval] using h

/-- Actual V-product moments averaged over the remaining original inputs are
the original pinned mean. This is the bridge needed to average the Harris
cross terms; the representation and block tower are both discharged. -/
theorem finiteJointHybridEval_product_block_integral
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (c cutoff : ℕ) (U V : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    (T : FiniteRevealTree E ∅) (hcN : c ≤ Fintype.card E) (hc : c ≤ cutoff) :
    (∫ W, ∫ v, g (finiteJointHybridEval w f cutoff W (finiteSeedExtension (Fintype.card E) V v)
      T ∅ ∅ false) ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
      ∂finiteOriginalPinBlock c (Fintype.card E - c) U) = finitePinnedMean w ∅ ∅ g := by
  have hp (W : ℕ → ℝ) := finiteJointHybridEval_product_integral w f g cutoff W V background T
  simp_rw [hp]
  have h := finiteJointHybridEval_pin_block_integral w f g hg01 c (Fintype.card E - c)
    cutoff U background T ∅ ∅ false (Fintype.card E) (by simp) hc
  simpa only [Finset.card_empty, Nat.add_sub_of_le hcN] using h

end
end PottsContinuity.BD12
