module

public import PottsContinuity.BD12.OriginalPinBlock
public import PottsContinuity.BD12.SeedWindowPinTower
public import PottsContinuity.BD12.ProbabilityKernelIntegral
public import PottsContinuity.BD12.HybridSeedMoments
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Separation.CompletelyRegular

/-! Integral towers and past-coordinate preservation for original-input blocks.
These identify which factors can be held fixed when original future inputs are
averaged in DRT's cross-moment estimate. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Coordinates outside the resampled block retain exactly their given value. -/
theorem finiteOriginalPinBlock_map_outside (c k : ℕ) (U : ℕ → ℝ) (i : ℕ)
    (hi : i < c ∨ c + k ≤ i) :
    (finiteOriginalPinBlock c k U).map (fun W => W i) = Measure.dirac (U i) := by
  induction k generalizing c U with
  | zero =>
    rw [finiteOriginalPinBlock, Measure.map_dirac' (measurable_pi_apply i)]
  | succ k ih =>
    have hK : Measurable (fun u : ℝ => finiteOriginalPinBlock (c + 1) k (Function.update U c u)) :=
      (finiteOriginalPinBlock_measurable (c + 1) k).comp (measurable_original_stream_update U c)
    rw [finiteOriginalPinBlock, finiteKernel_map_bind _ _ hK (fun W => W i) (measurable_pi_apply i)]
    have hchild : i < c + 1 ∨ (c + 1) + k ≤ i := by omega
    simp_rw [ih (c + 1) _ hchild, Function.update_of_ne (show i ≠ c by omega)]
    rw [Measure.bind_const, measure_univ, one_smul]

/-- Every coordinate of the earlier original prefix is preserved almost surely. -/
theorem finiteOriginalPinBlock_ae_past (c k : ℕ) (U : ℕ → ℝ) :
    ∀ᵐ W ∂finiteOriginalPinBlock c k U, ∀ i, i < c → W i = U i := by
  rw [ae_all_iff]
  intro i
  by_cases hi : i < c
  · have hmap := finiteOriginalPinBlock_map_outside c k U i (Or.inl hi)
    have h : ∀ᵐ x : ℝ ∂(finiteOriginalPinBlock c k U).map (fun W => W i), x = U i := by
      rw [hmap]
      simp
    have hcoord : ∀ᵐ W ∂finiteOriginalPinBlock c k U, W i = U i :=
      ae_of_ae_map (measurable_pi_apply i).aemeasurable h
    exact hcoord.mono (fun W hW _ => hW)
  · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)

/-- A factor depending only on the earlier original prefix is unchanged under
its future-block integral. This is a structural dependence premise, with its
support property proved above, not an expectation conclusion. -/
theorem finiteOriginalPinBlock_integral_past_factor (c k : ℕ) (U : ℕ → ℝ)
    (F G : (ℕ → ℝ) → ℝ)
    (hF : ∀ W, (∀ i, i < c → W i = U i) → F W = F U) :
    (∫ W, F W * G W ∂finiteOriginalPinBlock c k U) =
      F U * ∫ W, G W ∂finiteOriginalPinBlock c k U := by
  calc
    _ = ∫ W, F U * G W ∂finiteOriginalPinBlock c k U :=
      integral_congr_ae ((finiteOriginalPinBlock_ae_past c k U).mono
        (fun W hW => by rw [hF W hW]))
    _ = _ := integral_const_mul _ _

/-- Real observable tower through an arbitrary finite block of original inputs. -/
theorem finiteOriginalPinBlock_seed_integral (c k : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ)
    (g : (ℕ → ℝ × ℝ) → ℝ) (hg : Measurable g)
    (hg01 : ∀ S, g S ∈ Set.Icc (0 : ℝ) 1) :
    (∫ W, ∫ S, g S ∂finiteHybridSeedWindow (c + k) W background start n
      ∂finiteOriginalPinBlock c k U) =
      ∫ S, g S ∂finiteHybridSeedWindow c U background start n := by
  rw [probabilityKernel_unit_integral_bind _ _
    (finiteHybridSeedWindow_fixedU_measurable (c + k) background start n) g hg hg01,
    finiteOriginalPinBlock_seedWindow_tower]

/-- Averaging the actual hybrid observable over a newly fixed original block
recovers its pinned moment, even when the intermediate prefix exceeds cutoff. -/
theorem finiteJointHybridEval_pin_block_integral {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (c k cutoff : ℕ) (U : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) (hc : c ≤ cutoff) :
    (∫ W, ∫ S, g (finiteJointHybridEval w f cutoff
      (fun i => (S i).1) (fun i => (S i).2) T HX HY stopped)
      ∂finiteHybridSeedWindow (c + k) W background R.card n
      ∂finiteOriginalPinBlock c k U) = finitePinnedMean w R HY g := by
  have hmap : Measurable (fun S : ℕ → ℝ × ℝ => finiteJointHybridEval w f cutoff
      (fun i => (S i).1) (fun i => (S i).2) T HX HY stopped) :=
    (finiteJointHybridEval_measurable w f cutoff T HX HY stopped).comp
      (show Measurable (fun S : ℕ → ℝ × ℝ => ((fun i => (S i).1), (fun i => (S i).2))) by fun_prop)
  rw [finiteOriginalPinBlock_seed_integral c k U background R.card n
    (fun S => g (finiteJointHybridEval w f cutoff
      (fun i => (S i).1) (fun i => (S i).2) T HX HY stopped))
    ((measurable_of_finite g).comp hmap) (fun S => hg01 _),
    finiteJointHybridEval_seedWindow_integral w f g c cutoff U background T HX HY stopped n hn hc]

end
end PottsContinuity.BD12
