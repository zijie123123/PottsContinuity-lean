module

public import PottsContinuity.Thm3.Prop4.CorridorRows

/-!
# Capped horizontal positions of the overlapping corridor rectangles

The final stages stay at the rightmost permitted rectangle. This avoids a
special last rectangle extending outside the original box and retains an
integral step between zero and s at every stage.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The arithmetic ramp of rectangle anchors, capped at the rightmost permitted anchor. -/
def corridorAbscissa (n s : ℕ) (i : ℕ) : ℤ :=
  min (-(n : ℤ)+(i : ℤ)*(s : ℤ)) ((n : ℤ)-2*(s : ℤ))

/-- A rectangle of width 2s at this anchor stays inside the box horizontally. -/
theorem corridorAbscissa_bounds (n s : ℕ) (hs : s ≤ n) (i : ℕ) :
    -(n : ℤ) ≤ corridorAbscissa n s i ∧ corridorAbscissa n s i ≤ (n : ℤ)-2*(s : ℤ) := by
  have hi : 0 ≤ (i : ℤ)*(s : ℤ) := mul_nonneg (Int.natCast_nonneg i) (Int.natCast_nonneg s)
  dsimp [corridorAbscissa]
  omega

/-- Consecutive anchors move right by at most s, including the terminal plateau. -/
theorem corridorAbscissa_step (n s i : ℕ) :
    0 ≤ corridorAbscissa n s (i+1)-corridorAbscissa n s i ∧
      corridorAbscissa n s (i+1)-corridorAbscissa n s i ≤ (s : ℤ) := by
  simp only [corridorAbscissa,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
  omega

/-- The first rectangle starts at the original left face. -/
theorem corridorAbscissa_zero (n s : ℕ) (hs : s ≤ n) :
    corridorAbscissa n s 0 = -(n : ℤ) := by
  simp only [corridorAbscissa,Nat.cast_zero,zero_mul,add_zero]
  exact min_eq_left (by omega)

/-- By stage 2n every positive integral step has reached the final permitted rectangle. -/
theorem corridorAbscissa_last (n s : ℕ) (_hs : s ≤ n) (hspos : 1 ≤ s) :
    corridorAbscissa n s (2*n) = (n : ℤ)-2*(s : ℤ) := by
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast hspos
  have hm : 2*(n : ℤ) ≤ 2*(n : ℤ)*(s : ℤ) := by
    have h := mul_nonneg (show (0 : ℤ) ≤ 2*(n : ℤ) by omega) (sub_nonneg.mpr hs1)
    nlinarith only [h]
  simp only [corridorAbscissa,Nat.cast_mul,Nat.cast_ofNat]
  apply min_eq_right
  omega

end PottsContinuity.Thm3.Prop4
