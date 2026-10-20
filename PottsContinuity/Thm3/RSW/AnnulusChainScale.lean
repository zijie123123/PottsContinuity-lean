module

public import PottsContinuity.Thm3.RSW.CorridorScale

/-!
# Integer scales for P5b(R=8) to buffered P5

DCST TeX line 1021 uses nonintegral radii and centers. Use floor(n/16),
integer centers and an explicitly bounded number of windows instead.
These statements concern only the exact floor geometry, not circuit gluing.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- A positive mesoscopic radius with fixed deterministic comparison to n. -/
theorem annulus_chain_radius_bounds (n : ℕ) (hn : 32 ≤ n) :
    1 ≤ n/16 ∧ 16*(n/16) ≤ n ∧ n ≤ 32*(n/16) := by
  omega

/-- Integer circuit centers cover the target width with uniformly many steps.
The target endpoint is exactly the frozen floor, and width zero is allowed. -/
theorem exists_annulus_chain_length (α : ℝ) (hα : 0 < α)
    (n m : ℕ) (hm : 1 ≤ m) (hnm : n ≤ 32*m) :
    ∃ K : ℕ, ⌊α*(n:ℝ)⌋ ≤ (K*m:ℕ) ∧
      (K*m:ℕ) < ⌊α*(n:ℝ)⌋+(m:ℤ) ∧ K ≤ ⌈32*α+1⌉₊ := by
  have hA0 : (0:ℤ) ≤ ⌊α*(n:ℝ)⌋ := Int.floor_nonneg.mpr (mul_nonneg hα.le (Nat.cast_nonneg n))
  let A := (⌊α*(n:ℝ)⌋).toNat
  have hA : (A:ℤ) = ⌊α*(n:ℝ)⌋ := Int.toNat_of_nonneg hA0
  let K := (A+m-1)/m
  have hrem := Nat.mod_lt (A+m-1) (show 0 < m from hm)
  have heq : K*m+(A+m-1)%m = A+m-1 := by
    simpa only [K,Nat.mul_comm] using Nat.div_add_mod (A+m-1) m
  have hcover : A ≤ K*m := by omega
  have hprod : K*m ≤ A+m-1 := Nat.div_mul_le_self _ _
  have hspan : K*m < A+m := by omega
  have hfloor : (A:ℝ) ≤ α*(n:ℝ) := by
    have h := Int.floor_le (α*(n:ℝ))
    have hcast : (A:ℝ) = (⌊α*(n:ℝ)⌋:ℝ) := by exact_mod_cast hA
    rwa [← hcast] at h
  have hnR : (n:ℝ) ≤ 32*(m:ℝ) := by exact_mod_cast hnm
  have hspanR : (K:ℝ)*(m:ℝ) < (A:ℝ)+(m:ℝ) := by exact_mod_cast hspan
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hK : (K:ℝ) < 32*α+1 := by
    have hwidth := mul_le_mul_of_nonneg_left hnR hα.le
    have hmul : (K:ℝ)*(m:ℝ) < (32*α+1)*(m:ℝ) := by
      nlinarith only [hspanR,hfloor,hwidth]
    exact (mul_lt_mul_iff_right₀ hmR).mp (by simpa only [mul_comm] using hmul)
  refine ⟨K,?_,?_,?_⟩
  · rw [← hA]
    exact_mod_cast hcover
  · rw [← hA]
    exact_mod_cast hspan
  · have hceil : (K:ℝ) ≤ (⌈32*α+1⌉₊:ℝ) := hK.le.trans (Nat.le_ceil _ )
    exact_mod_cast hceil

/-- Adding the integer buffer to the aspect preserves the exact right floor. -/
theorem buffered_right_floor_eq (α : ℝ) (n : ℕ) :
    ⌊(α+1)*(n:ℝ)⌋ = ⌊α*(n:ℝ)⌋+(n:ℤ) := by
  rw [add_mul,one_mul,Int.floor_add_natCast]

end PottsContinuity.RSW
