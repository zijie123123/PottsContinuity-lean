module

public import PottsContinuity.BD12.JointHybridRegularity

/-! The DRT switch identity for the actual adaptive hybrid continuation. The
original branching and stopping history stay fixed, while one fresh hybrid
threshold input is switched. Preservation of its revealed coordinate and
comparability are proved from the actual recursion. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Once both cutoffs are in the past, they yield identical remaining inputs. -/
theorem finiteJointHybridEval_cutoffs_in_past (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (s t : ℕ) (U V : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (hs : s ≤ R.card) (ht : t ≤ R.card) :
    finiteJointHybridEval w f s U V T HX HY stopped =
      finiteJointHybridEval w f t U V T HX HY stopped := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    simp only [finiteJointHybridEval, hs, ht, true_and]
    apply ih
    · exact hs.trans (Finset.card_mono (Finset.subset_insert e R))
    · exact ht.trans (Finset.card_mono (Finset.subset_insert e R))

/-- DRT's switch identity for the common-space adaptive continuation following a
switched edge. The edge is already in the revealed index of the continuation,
so its bit cannot be resampled on any future original branch. -/
theorem finiteJointHybridContinuation_switch_abs
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g : Finset E → ℝ) (hg : Monotone g) (cutoff : ℕ) (U V : ℕ → ℝ)
    (R H HX : Finset E) (e : E) (T : FiniteRevealTree E (insert e R))
    (stopped : Bool) (x y : ℝ) :
    let A := finiteJointHybridEval w f cutoff U V T HX (finiteThresholdStep w R H e x) stopped
    let B := finiteJointHybridEval w f cutoff U V T HX (finiteThresholdStep w R H e y) stopped
    |g A - g B| = (g A - g B) *
      ((if e ∈ A then (1 : ℝ) else 0) - (if e ∈ B then (1 : ℝ) else 0)) := by
  let O := finiteJointHybridEval w f cutoff U V T HX (insert e H) stopped
  let C := finiteJointHybridEval w f cutoff U V T HX (H.erase e) stopped
  have hO : e ∈ O := by
    have h : e ∈ O ∩ insert e R := by
      rw [finiteJointHybridEval_inter]
      simp
    exact (Finset.mem_inter.mp h).1
  have hC : e ∉ C := by
    intro h
    have hi : e ∈ C ∩ insert e R := Finset.mem_inter.mpr ⟨h, by simp⟩
    rw [finiteJointHybridEval_inter] at hi
    simp at hi
  have hCO : C ⊆ O := finiteJointHybridEval_monotone w hw f cutoff U T HX
    ((Finset.erase_subset e H).trans (Finset.subset_insert e H)) stopped le_rfl
  have hgCO := hg hCO
  dsimp only
  unfold finiteThresholdStep
  by_cases hx : 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ x
  · by_cases hy : 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ y
    · simp only [ite_eq_left hx, ite_eq_left hy, sub_self, abs_zero, zero_mul]
    · simp only [ite_eq_left hx, ite_eq_right hy]
      change |g O - g C| = (g O - g C) *
        ((if e ∈ O then (1 : ℝ) else 0) - (if e ∈ C then (1 : ℝ) else 0))
      rw [ite_eq_left hO, ite_eq_right hC, sub_zero, mul_one,
        abs_of_nonneg (sub_nonneg.mpr hgCO)]
  · by_cases hy : 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ y
    · simp only [ite_eq_right hx, ite_eq_left hy]
      change |g C - g O| = (g C - g O) *
        ((if e ∈ C then (1 : ℝ) else 0) - (if e ∈ O then (1 : ℝ) else 0))
      rw [ite_eq_right hC, ite_eq_left hO, zero_sub, mul_neg_one,
        abs_of_nonpos (sub_nonpos.mpr hgCO)]
    · simp only [ite_eq_right hx, ite_eq_right hy, sub_self, abs_zero, zero_mul]

/-- The four-term form for the actual adaptive continuation. -/
theorem finiteJointHybridContinuation_switch_identity
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g : Finset E → ℝ) (hg : Monotone g) (cutoff : ℕ) (U V : ℕ → ℝ)
    (R H HX : Finset E) (e : E) (T : FiniteRevealTree E (insert e R))
    (stopped : Bool) (x y : ℝ) :
    let A := finiteJointHybridEval w f cutoff U V T HX (finiteThresholdStep w R H e x) stopped
    let B := finiteJointHybridEval w f cutoff U V T HX (finiteThresholdStep w R H e y) stopped
    |g A - g B| = g A * (if e ∈ A then 1 else 0) + g B * (if e ∈ B then 1 else 0) -
      g A * (if e ∈ B then 1 else 0) - g B * (if e ∈ A then 1 else 0) := by
  dsimp only
  rw [finiteJointHybridContinuation_switch_abs w hw f g hg cutoff U V R H HX e T stopped x y]
  ring


/-- Adjacent actual hybrid cutoffs at the current query obey DRT's four-term
identity, including the case where the stopping rule has already fired. -/
theorem finiteJointHybrids_adjacent_query_identity
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g : Finset E → ℝ) (hg : Monotone g) (U V : ℕ → ℝ)
    (R HX HY : Finset E) (e : E) (he : e ∉ R)
    (next : Bool → FiniteRevealTree E (insert e R)) (stopped : Bool) :
    let A := finiteJointHybridEval w f (R.card + 1) U V (.query e he next) HX HY stopped
    let B := finiteJointHybridEval w f R.card U V (.query e he next) HX HY stopped
    |g A - g B| = g A * (if e ∈ A then 1 else 0) + g B * (if e ∈ B then 1 else 0) -
      g A * (if e ∈ B then 1 else 0) - g B * (if e ∈ A then 1 else 0) := by
  let halted := stopped || decide (finiteDetermines f R HX)
  let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0))
    (U R.card)
  let HX' := finiteRevealPattern HX e bx
  let y := if halted = false then U R.card else V R.card
  have hA : finiteJointHybridEval w f (R.card + 1) U V (.query e he next) HX HY stopped =
      finiteJointHybridEval w f (R.card + 1) U V (next bx) HX'
        (finiteThresholdStep w R HY e (V R.card)) halted := by
    dsimp only [HX', bx, halted]
    simp only [finiteJointHybridEval, Nat.not_succ_le_self, false_and, ite_false,
      finiteRevealPattern_uniformBit]
  have hB : finiteJointHybridEval w f R.card U V (.query e he next) HX HY stopped =
      finiteJointHybridEval w f (R.card + 1) U V (next bx) HX'
        (finiteThresholdStep w R HY e y) halted := by
    dsimp only [HX', bx, halted, y]
    simp only [finiteJointHybridEval, le_refl, true_and, finiteRevealPattern_uniformBit]
    apply finiteJointHybridEval_cutoffs_in_past
    · exact Finset.card_mono (Finset.subset_insert e R)
    · rw [Finset.card_insert_of_notMem he]
  dsimp only
  rw [hA, hB]
  exact finiteJointHybridContinuation_switch_identity w hw f g hg (R.card + 1) U V
    R HY HX' e (next bx) halted (V R.card) y

end
end PottsContinuity.BD12
