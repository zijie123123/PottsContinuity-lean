module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# Digital centers of the rectangular corridor

Round the supporting-line height down, then project to the nonempty integer
interval leaving s rows on either side inside the original square. The
projection is defined with its honest nonemptiness proof.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Integer interval projection does not enlarge coordinate differences. -/
theorem integer_projIcc_abs_sub_le (a b x y : ℤ) (hab : a ≤ b) :
    |(Set.projIcc a b hab x : ℤ)-(Set.projIcc a b hab y : ℤ)| ≤ |x-y| := by
  dsimp [Set.projIcc]
  simp only [abs_eq_max_neg]
  omega

/-- The actual integer center row, rounded from the supporting line and kept inside the square. -/
noncomputable def corridorRow (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (x : ℤ) : ℤ :=
  (Set.projIcc (-(n : ℤ)+(s : ℤ)) ((n : ℤ)-(s : ℤ)) (by omega) ⌊t*(x : ℝ)+b⌋).val

/-- Every corridor rectangle centered on this row has s rows of room on both sides. -/
theorem corridorRow_bounds (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (x : ℤ) :
    -(n : ℤ)+(s : ℤ) ≤ corridorRow n s hs t b x ∧
      corridorRow n s hs t b x ≤ (n : ℤ)-(s : ℤ) :=
  (Set.projIcc _ _ (by omega) ⌊t*(x : ℝ)+b⌋).property

/-- Rounding a slope of absolute value at most one respects every integral step bound. -/
theorem corridorRow_step (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (ht : |t| ≤ 1)
    (x y : ℤ) (k : ℕ) (hxy : |x-y| ≤ (k : ℤ)) :
    |corridorRow n s hs t b x-corridorRow n s hs t b y| ≤ (k : ℤ) := by
  have hxyR : |(x : ℝ)-(y : ℝ)| ≤ (k : ℝ) := by exact_mod_cast hxy
  have hp : |t*((x : ℝ)-(y : ℝ))| ≤ (k : ℝ) := by
    rw [abs_mul]
    calc
      _ ≤ 1*|(x : ℝ)-(y : ℝ)| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hxyR
  have hA : t*(x : ℝ)+b ≤ (t*(y : ℝ)+b)+(k : ℝ) := by
    have := (abs_le.mp hp).2
    nlinarith only [this]
  have hB : t*(y : ℝ)+b ≤ (t*(x : ℝ)+b)+(k : ℝ) := by
    have := (abs_le.mp hp).1
    nlinarith only [this]
  have hAf := Int.floor_mono hA
  have hBf := Int.floor_mono hB
  rw [Int.floor_add_natCast] at hAf hBf
  have hf : |⌊t*(x : ℝ)+b⌋-⌊t*(y : ℝ)+b⌋| ≤ (k : ℤ) := by
    rw [abs_le]
    omega
  exact (integer_projIcc_abs_sub_le _ _ _ _ (by omega)).trans hf

/-- A line height within the square moves by less than s+1 under rounding and projection. -/
theorem corridorRow_line_deviation (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (x : ℤ)
    (hline : -(n : ℝ) ≤ t*(x : ℝ)+b ∧ t*(x : ℝ)+b ≤ n) :
    |(corridorRow n s hs t b x : ℝ)-(t*(x : ℝ)+b)| < (s : ℝ)+1 := by
  have hlo : -(n : ℤ) ≤ ⌊t*(x : ℝ)+b⌋ := Int.le_floor.mpr (by exact_mod_cast hline.1)
  have hhiR : (⌊t*(x : ℝ)+b⌋ : ℝ) ≤ n := (Int.floor_le _).trans hline.2
  have hhi : ⌊t*(x : ℝ)+b⌋ ≤ (n : ℤ) := by exact_mod_cast hhiR
  have hdiff : |corridorRow n s hs t b x-⌊t*(x : ℝ)+b⌋| ≤ (s : ℤ) := by
    dsimp [corridorRow,Set.projIcc]
    simp only [abs_eq_max_neg]
    omega
  have hdiffR : |(corridorRow n s hs t b x : ℝ)-(⌊t*(x : ℝ)+b⌋ : ℝ)| ≤ (s : ℝ) := by
    exact_mod_cast hdiff
  have hflo := Int.floor_le (t*(x : ℝ)+b)
  have hfhi := Int.lt_floor_add_one (t*(x : ℝ)+b)
  apply abs_lt.mpr
  constructor <;> linarith only [(abs_le.mp hdiffR).1,(abs_le.mp hdiffR).2,hflo,hfhi]

end PottsContinuity.Thm3.Prop4
