module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

/-!
# Discrete descent for Lemma 6

DCST (15 May 2015), TeX lines 1595–1603, the deterministic local-minimum
pigeonhole step. The natural height records the height in units of 1/m.
There is no strip law, top-connected-set definition, or probabilistic premise.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Descent of a nonnegative integer height finds an m-local minimum within
height-times-m of the starting column. No global upper height bound is needed. -/
theorem exists_local_minimum_nat_height (f : ℤ → ℕ) (m : ℕ) (x : ℤ) :
    ∃ k : ℤ, |k - x| ≤ (f x : ℤ) * m ∧ f k ≤ f x ∧
      ∀ j : ℤ, |j - k| ≤ (m : ℤ) → f k ≤ f j := by
  suffices h : ∀ r : ℕ, ∀ x : ℤ, f x ≤ r →
      ∃ k : ℤ, |k - x| ≤ (f x : ℤ) * m ∧ f k ≤ f x ∧
        ∀ j : ℤ, |j - k| ≤ (m : ℤ) → f k ≤ f j from h (f x) x le_rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro x hx
    by_cases hmin : ∀ j : ℤ, |j - x| ≤ (m : ℤ) → f x ≤ f j
    · exact ⟨x, by simpa using (mul_nonneg (Int.natCast_nonneg (f x))
          (Int.natCast_nonneg m)), le_rfl, hmin⟩
    · push Not at hmin
      obtain ⟨j, hj, hjf⟩ := hmin
      obtain ⟨k, hkj, hfk, hkmin⟩ := ih (f j) (hjf.trans_le hx) j le_rfl
      refine ⟨k, ?_, hfk.trans hjf.le, hkmin⟩
      have hstep : (f j : ℤ) + 1 ≤ f x := by exact_mod_cast hjf
      calc
        |k - x| ≤ |k - j| + |j - x| := abs_sub_le k j x
        _ ≤ (f j : ℤ) * m + m := add_le_add hkj hj
        _ ≤ (f x : ℤ) * m := by
          have := mul_le_mul_of_nonneg_right hstep (Int.natCast_nonneg m)
          nlinarith only [this]

/-- The radius nm² in the source follows from a starting discrete height ≤nm.
This is the integral-height combinatorial step, not a touch probability bound. -/
theorem local_minimum_in_source_window (f : ℤ → ℕ) (n m : ℕ)
    (hzero : f 0 ≤ n * m) :
    ∃ k : ℤ, |k| ≤ (n : ℤ) * (m : ℤ)^2 ∧ f k ≤ n * m ∧
      ∀ j : ℤ, |j - k| ≤ (m : ℤ) → f k ≤ f j := by
  obtain ⟨k, hk, hfk, hmin⟩ := exists_local_minimum_nat_height f m 0
  refine ⟨k, ?_, hfk.trans hzero, hmin⟩
  have hzeroZ : (f 0 : ℤ) ≤ (n : ℤ) * m := by exact_mod_cast hzero
  calc
    |k| ≤ (f 0 : ℤ) * m := by simpa only [sub_zero] using hk
    _ ≤ ((n : ℤ) * m) * m :=
      mul_le_mul_of_nonneg_right hzeroZ (Int.natCast_nonneg m)
    _ = (n : ℤ) * (m : ℤ)^2 := by ring

/-- The source's real-height pigeonhole statement. Discreteness is explicit:
each nonnegative height is an integer multiple of 1/m. No assumption of a
local minimum or a probabilistic conclusion is used. -/
theorem exists_local_minimum_discrete_height (F : ℤ → ℝ) (n m : ℕ)
    (hm : 1 ≤ m) (hF : ∀ k : ℤ, ∃ j : ℕ, F k = (j : ℝ) / m)
    (hzero : F 0 ≤ n) :
    ∃ k : ℤ, |k| ≤ (n : ℤ) * (m : ℤ)^2 ∧ F k ≤ n ∧
      ∀ j : ℤ, |j - k| ≤ (m : ℤ) → F k ≤ F j := by
  let f : ℤ → ℕ := fun k => ⌊F k * (m : ℝ)⌋₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : ∀ k : ℤ, (f k : ℝ) = F k * (m : ℝ) := by
    intro k
    obtain ⟨j, hj⟩ := hF k
    dsimp [f]
    rw [hj, div_mul_cancel₀ _ hmR.ne']
    simp only [Nat.floor_natCast]
  have hfzero : f 0 ≤ n * m := by
    have h : (f 0 : ℝ) ≤ (n : ℝ) * m := by
      rw [hf]
      exact mul_le_mul_of_nonneg_right hzero hmR.le
    exact_mod_cast h
  obtain ⟨k, hk, hkn, hmin⟩ := local_minimum_in_source_window f n m hfzero
  refine ⟨k, hk, ?_, ?_⟩
  · have h : (f k : ℝ) ≤ (n : ℝ) * m := by exact_mod_cast hkn
    rw [hf] at h
    exact (mul_le_mul_iff_left₀ hmR).mp (by simpa only [mul_comm] using h)
  · intro j hj
    have h : (f k : ℝ) ≤ f j := by exact_mod_cast hmin j hj
    rw [hf, hf] at h
    exact (mul_le_mul_iff_left₀ hmR).mp (by simpa only [mul_comm] using h)

end PottsContinuity.Thm3.Prop4
