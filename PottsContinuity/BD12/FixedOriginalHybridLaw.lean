module

public import PottsContinuity.BD12.FixedOriginalSeedProduct
public import PottsContinuity.BD12.HybridSeedIdentification

/-! Identification of the actual finite-V-product hybrid family with its fully
fixed-original-input seed kernel. The background outside the sampled coordinates
may be chosen independently of the prescribed original stream. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    [MeasurableSpace (Finset E)]

omit [Fintype ι] in
/-- The joint completed output law ignores the seed background outside the
sampled window, for every original prefix length and every family of cutoffs. -/
theorem finiteHybridFamilyEval_seed_background_congr
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (U : ℕ → ℝ) (cutoff : ι → ℕ)
    (background background' : ℕ → ℝ × ℝ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (HY : ι → Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) :
    (finiteHybridSeedWindow fixedThrough U background R.card n).map
        (finiteHybridFamilyEval w f cutoff T HX HY stopped) =
      (finiteHybridSeedWindow fixedThrough U background' R.card n).map
        (finiteHybridFamilyEval w f cutoff T HX HY stopped) := by
  rw [finiteHybridFamilyEval_map_seedWindow w f fixedThrough U cutoff background T HX HY stopped n hn,
    finiteHybridFamilyEval_map_seedWindow w f fixedThrough U cutoff background' T HX HY stopped n hn]

omit [Fintype ι] in
/-- Joint law of the actual original sample and every hybrid on the same
finite replacement-product space, with U fixed. -/
theorem finiteFixedHybridFamily_product_eq_seedWindow
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U V : ℕ → ℝ) (cutoff : ι → ℕ) (background : ℕ → ℝ × ℝ)
    (T : FiniteRevealTree E ∅) :
    (Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)).map
        (fun v => (finiteOriginalEval w U T ∅,
          fun j => finiteJointHybridEval w f (cutoff j) U
            (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)) =
      (finiteHybridSeedWindow (Fintype.card E) U background 0 (Fintype.card E)).map
        (finiteHybridFamilyEval w f cutoff T ∅ (fun _ => ∅) false) := by
  let N := Fintype.card E
  let S := fun v : Fin N → ℝ => fun i => (U i, finiteSeedExtension N V v i)
  let F := finiteHybridFamilyEval w f cutoff T ∅ (fun _ => ∅) false
  have hS : Measurable S := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.prodMk ((measurable_pi_apply i).comp (finiteSeedExtension_measurable N V))
  have hF : Measurable F := finiteHybridFamilyEval_measurable w f cutoff T ∅ (fun _ => ∅) false
  change (Measure.pi (fun _ : Fin N => finiteUnitUniform)).map (F ∘ S) = _
  rw [← Measure.map_map hF hS, finiteFixedOriginal_seed_product]
  have h := finiteHybridFamilyEval_seed_background_congr w f N U cutoff
    (fun i => (U i, V i)) background T ∅ (fun _ => ∅) false N (by simp [N])
  simpa only [Finset.card_empty] using h

end
end PottsContinuity.BD12
