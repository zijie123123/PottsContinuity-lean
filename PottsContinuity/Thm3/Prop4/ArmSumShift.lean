module

public import PottsContinuity.Thm3.Prop4.OneArmRatio
public import PottsContinuity.Thm3.Prop4.PairKernel
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# The exact two-unit convolution shift in equation (30)

Both endpoint arm radii increase by one. The real cutoff is retained exactly;
there is no floor shift or discarded small-scale case.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The complete nonnegative split-arm convolution at a real lower cutoff. -/
noncomputable def splitArmSum (a : ℕ → ℝ) (r : ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.range (N+1), if r ≤ k ∧ r ≤ (N-k : ℕ) then a k*a (N-k) else 0

theorem splitArmSum_shift_two (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (D : ℝ) (hD : 0 ≤ D) (hratio : ∀ k, a k ≤ D*a (k+1)) (r : ℝ) (N : ℕ) :
    splitArmSum a r N ≤ D^2*splitArmSum a r (N+2) := by
  classical
  let f : ℕ → ℝ := fun k => if r ≤ k ∧ r ≤ (N+2-k : ℕ) then a k*a (N+2-k) else 0
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    split_ifs
    · exact mul_nonneg (ha _) (ha _)
    · exact le_rfl
  have hpoint (k : ℕ) (hk : k ∈ Finset.range (N+1)) :
      (if r ≤ k ∧ r ≤ (N-k : ℕ) then a k*a (N-k) else 0) ≤ D^2*f (k+1) := by
    have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
    by_cases hc : r ≤ k ∧ r ≤ (N-k : ℕ)
    · have hsub : N+2-(k+1)=N-k+1 := by omega
      have hnew : r ≤ (k+1 : ℕ) ∧ r ≤ (N+2-(k+1) : ℕ) := by
        rw [hsub]
        constructor
        · exact hc.1.trans (by exact_mod_cast Nat.le_succ k)
        · exact hc.2.trans (by exact_mod_cast Nat.le_succ (N-k))
      dsimp [f]
      rw [ite_eq_left hc,ite_eq_left hnew,hsub]
      have h := mul_le_mul (hratio k) (hratio (N-k)) (ha (N-k))
        (mul_nonneg hD (ha (k+1)))
      nlinarith only [h]
    · rw [ite_eq_right hc]
      exact mul_nonneg (sq_nonneg D) (hf _)
  have hsum : (∑ k ∈ Finset.range (N+1), f (k+1)) ≤
      ∑ k ∈ Finset.range (N+3), f k := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ (N+1))) (f := fun k => f (k+1))
      (fun k _ _ => hf (k+1))
    have heq := Finset.sum_range_succ' f (N+2)
    linarith only [hle,heq,hf 0]
  unfold splitArmSum
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), D^2*f (k+1) := Finset.sum_le_sum hpoint
    _ = D^2*∑ k ∈ Finset.range (N+1), f (k+1) := by rw [Finset.mul_sum]
    _ ≤ D^2*∑ k ∈ Finset.range (N+3), f k :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg D)
    _ = _ := rfl

/-- The actual source one-arm convolution shifts from 2n-2 to 2n uniformly
in the cutoff, with a parameter-only finite-energy factor. -/
theorem oneArm_split_sum_shift (θ : PD.FK.Parameters)
    (μ : MeasureTheory.Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (r : ℝ) (n : ℕ), 1 ≤ n →
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) ≤
        D^2*splitArmSum (RSW.oneArmProbability μ) r (2*n) := by
  obtain ⟨D,hD,hratio⟩ := oneArm_probability_upper_ratio θ μ hμ
  refine ⟨D,hD,?_⟩
  intro r n hn
  have h := splitArmSum_shift_two (RSW.oneArmProbability μ) (fun _ => ENNReal.toReal_nonneg)
    D (by linarith only [hD]) hratio r (2*n-2)
  have heq : 2*n-2+2=2*n := by omega
  simpa only [heq] using h

end PottsContinuity.Thm3.Prop4
