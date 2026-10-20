module

public import PottsContinuity.BD12.OriginalPinBlock
public import PottsContinuity.BD12.JointHybridAssociation
public import PottsContinuity.BD12.FiniteSeedWindow

/-! Pair-valued finite seed insertion with the original U inputs prescribed
and the replacement V inputs supplied by a finite vector. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Insert the pairs (U_i,v_i) on the indicated consecutive window, retaining
the specified pair-valued background everywhere else. -/
def finiteFixedOriginalExtension : (start n : ℕ) → (ℕ → ℝ) → (ℕ → ℝ × ℝ) →
    (Fin n → ℝ) → ℕ → ℝ × ℝ
  | _, 0, _, background, _ => background
  | start, n + 1, U, background, v =>
      Function.update (finiteFixedOriginalExtension (start + 1) n U background (fun j => v j.succ))
        start (U start, v 0)

theorem finiteFixedOriginalExtension_measurable (start n : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) :
    Measurable (finiteFixedOriginalExtension start n U background) := by
  induction n generalizing start with
  | zero => exact measurable_const
  | succ n ih =>
    have ht : Measurable (fun v : Fin (n + 1) → ℝ =>
        finiteFixedOriginalExtension (start + 1) n U background (fun j => v j.succ)) :=
      (ih (start + 1)).comp (measurable_pi_iff.mpr (fun j => measurable_pi_apply j.succ))
    have hh : Measurable (fun v : Fin (n + 1) → ℝ => (U start, v 0)) :=
      measurable_const.prodMk (measurable_pi_apply 0)
    exact (measurable_stream_update start).comp (hh.prodMk ht)

/-- Exact pair coordinates on the entire stream carrier. -/
theorem finiteFixedOriginalExtension_apply (start n : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (v : Fin n → ℝ) (i : ℕ) :
    finiteFixedOriginalExtension start n U background v i =
      if h : start ≤ i ∧ i < start + n then (U i, v ⟨i - start, by omega⟩) else background i := by
  induction n generalizing start with
  | zero => simp only [finiteFixedOriginalExtension, show ¬(start ≤ i ∧ i < start + 0) by omega, dite_false]
  | succ n ih =>
    rw [finiteFixedOriginalExtension]
    by_cases hi0 : i = start
    · subst i
      rw [Function.update_self, dite_eq_left (show start ≤ start ∧ start < start + (n + 1) by omega)]
      congr 1
      apply congrArg v
      apply Fin.ext
      simp
    · rw [Function.update_of_ne hi0, ih]
      by_cases hi : start + 1 ≤ i ∧ i < start + 1 + n
      · rw [dite_eq_left hi, dite_eq_left (show start ≤ i ∧ i < start + (n + 1) by omega)]
        congr 1
        apply congrArg v
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      · rw [dite_eq_right hi, dite_eq_right (show ¬(start ≤ i ∧ i < start + (n + 1)) by omega)]

/-- A compatible background makes the original stream literally U everywhere,
and the replacement stream literally the existing finiteSeedExtension. -/
theorem finiteFixedOriginalExtension_zero (n : ℕ) (U V : ℕ → ℝ) (v : Fin n → ℝ) :
    finiteFixedOriginalExtension 0 n U (fun i => (U i, V i)) v =
      fun i => (U i, finiteSeedExtension n V v i) := by
  funext i
  rw [finiteFixedOriginalExtension_apply]
  by_cases hi : i < n
  · simp only [Nat.zero_le, Nat.zero_add, true_and, hi, dite_true,
      Nat.sub_zero, finiteSeedExtension]
  · simp only [Nat.zero_le, Nat.zero_add, true_and, hi, dite_false, finiteSeedExtension]

end
end PottsContinuity.BD12
