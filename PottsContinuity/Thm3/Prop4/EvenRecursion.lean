module

public import PottsContinuity.Thm3.Prop4.ProductMaximum
public import PottsContinuity.Thm3.Prop4.ReweightedKernel
public import Mathlib.Tactic

/-!
# From the source summation estimate to an attained even recursion

DCST, TeX lines 1775–1785. This is a numerical implication with its source
summation premise exposed. It is not a model-specific Proposition 4 export.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The complete numerical maximum-extraction step. The explicit premise is the
reweighted summation bound supplied by the exterior-circuit and square estimates. -/
theorem even_product_recursion_of_summationBound (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hlim : Tendsto u atTop (𝓝 0))
    (C c ε β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1)
    (hsum : ∀ n : ℕ, 1 ≤ n → u (2*n) ≤
      Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β u m.1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ k l : ℕ, (n : ℝ)^ε ≤ k ∧ (n : ℝ)^ε ≤ l ∧ 2*n ≤ k+l ∧
        u (2*n) ≤ K*u k*u l := by
  classical
  obtain ⟨K,hK,hbound⟩ := prop4_analytic_sum_bound C c ε β hC hc hε hεβ hβ1
  refine ⟨K,hK,?_⟩
  intro n hn
  let S : Set (ℕ × ℕ) := {p | (n : ℝ)^ε ≤ p.1 ∧ (n : ℝ)^ε ≤ p.2 ∧ 2*n ≤ p.1+p.2}
  have hnε : (n : ℝ)^ε ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n by exact_mod_cast hn) (hεβ.trans hβ1).le
  have hS : S.Nonempty := ⟨(n,n),hnε,hnε,by omega⟩
  obtain ⟨p,hp,hmax⟩ := exists_product_maximum u hu hlim S hS
  let B := u p.1*u p.2
  have hB : 0 ≤ B := mul_nonneg (hu _) (hu _)
  have hprod : ∀ k l : ℕ, (n : ℝ)^ε ≤ k → (n : ℝ)^ε ≤ l →
      2*n ≤ k+l → u k*u l ≤ B := fun k l hk hl hkl => hmax (k,l) ⟨hk,hl,hkl⟩
  have hkernel := prop4Kernel_tail_summable C c ε β hC hc hε hεβ hβ1 n
  have hdom : ∀ m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β u m.1 ≤
      B*prop4Kernel C c ε β m.1 := fun m =>
    prop4ReweightedKernel_le_product C c ε β B u hC.le hc.le hε.le
      (hεβ.trans hβ1).le n m.1 hn m.2 hprod
  have hrew : Summable (fun m : {m : ℕ // n ≤ m} => prop4ReweightedKernel C c ε β u m.1) :=
    Summable.of_nonneg_of_le (fun m => prop4ReweightedKernel_nonneg C c ε β u hC.le hc.le hu m.1)
      hdom (hkernel.mul_left B)
  refine ⟨p.1,p.2,hp.1,hp.2.1,hp.2.2,?_⟩
  calc
    u (2*n) ≤ Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β u m.1) := hsum n hn
    _ ≤ Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, B*prop4Kernel C c ε β m.1) :=
      mul_le_mul_of_nonneg_left (hrew.tsum_le_tsum hdom (hkernel.mul_left B)) (Real.exp_nonneg _)
    _ = B*(Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4Kernel C c ε β m.1)) := by
      rw [tsum_mul_left]
      ring
    _ ≤ B*K := mul_le_mul_of_nonneg_left (hbound n hn) hB
    _ = K*u p.1*u p.2 := by dsimp [B]; ring

end PottsContinuity.Thm3.Prop4
