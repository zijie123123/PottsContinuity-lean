module

public import PottsContinuity.Thm3.RSW.AnnulusPositivity
public import PottsContinuity.Thm3.RSW.SevenfoldDecay

/-!
# Choosing the small scale and iterating the source annulus recurrence

DCST Proposition 3, TeX lines 1519–1528. Failure of a uniform positive circuit
bound yields the small starting scale directly; no unproved liminf claim is
used. The ladder estimate retains Lemma 4 as an explicit conditional input.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Failure of P5b at R=8 supplies the source starting scale for every positive
normalizing coefficient. This is the direct infimum argument in choose-n0. -/
theorem selfDual_annulus_small_scale (q : Set.Ici (1 : ℝ)) (C : ℝ) (hC : 0 < C)
    (hfail : ¬ ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ C * annulusProbability (selfDualParameters q) 8 n₀ < 1 := by
  classical
  by_contra hnone
  apply hfail
  refine ⟨1/C, one_div_pos.mpr hC, fun n hn => ?_⟩
  have hprod : 1 ≤ C * annulusProbability (selfDualParameters q) 8 n :=
    le_of_not_gt (fun h => hnone ⟨n, hn, h⟩)
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hprod)

/-- The exact source exponent and geometric-scale decay from the actual
annulus sequence. The source Lemma-4 recursion remains an explicit interface
until the exploration and circuit-screen geometry have been proved. -/
theorem selfDual_annulus_ladder_decay_of_induction1
    (q : Set.Ici (1 : ℝ)) (C : ℝ) (hC : 0 < C)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C * (annulusProbability (selfDualParameters q) 8 n)^2)
    (hfail : ¬ ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ d : ℝ, 0 < d ∧ ∀ k : ℕ,
      C * annulusProbability (selfDualParameters q) 8 (7^k*n₀) ≤
        Real.exp (-d * (((7^k*n₀ : ℕ) : ℝ)^sevenfoldExponent)) := by
  obtain ⟨n₀, hn₀, hsmall⟩ := selfDual_annulus_small_scale q C hC hfail
  let u (n : ℕ) := C * annulusProbability (selfDualParameters q) 8 n
  have hu : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg hC.le (annulusProbability_nonneg (selfDualParameters q) 8 n)
  have hrec : ∀ n, 1 ≤ n → u (7*n) ≤ (u n)^2 := by
    intro n hn
    calc
      u (7*n) ≤ C * (C * (annulusProbability (selfDualParameters q) 8 n)^2) :=
        mul_le_mul_of_nonneg_left (hinduction1 n hn) hC.le
      _ = (u n)^2 := by dsimp only [u]; ring
  obtain ⟨d, hd, hdecay⟩ := sevenfold_ladder_decay u hu hrec n₀ hn₀ hsmall
  exact ⟨n₀, hn₀, d, hd, hdecay⟩

end PottsContinuity.RSW
