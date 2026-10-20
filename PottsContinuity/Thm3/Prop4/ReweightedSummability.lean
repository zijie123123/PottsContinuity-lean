module

public import PottsContinuity.Thm3.Prop4.ReweightedKernel
public import Mathlib.Tactic

/-! # Actual summability of the reweighted source tails -/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- A bounded nonnegative sequence has summable reweighted source tails. -/
theorem prop4ReweightedKernel_tail_summable (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hub : BddAbove (Set.range u))
    (C c ε β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun m : {m : ℕ // n ≤ m} => prop4ReweightedKernel C c ε β u m.1) := by
  obtain ⟨B,hB⟩ := hub
  have hB0 : 0 ≤ B := (hu 0).trans (hB (Set.mem_range_self 0))
  have hprod : ∀ k l : ℕ, (n : ℝ)^ε ≤ k → (n : ℝ)^ε ≤ l →
      2*n ≤ k+l → u k*u l ≤ B^2 := by
    intro k l _ _ _
    simpa only [pow_two] using mul_le_mul (hB (Set.mem_range_self k))
      (hB (Set.mem_range_self l)) (hu l) hB0
  have hdom : ∀ m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β u m.1 ≤
      B^2*prop4Kernel C c ε β m.1 := fun m =>
    prop4ReweightedKernel_le_product C c ε β (B^2) u hC.le hc.le
      hε.le (hεβ.trans hβ1).le n m.1 hn m.2 hprod
  have hs := prop4Kernel_tail_summable C c ε β hC hc hε hεβ hβ1 n
  exact Summable.of_nonneg_of_le
    (fun m => prop4ReweightedKernel_nonneg C c ε β u hC.le hc.le hu m.1)
    hdom (hs.mul_left (B^2))

end PottsContinuity.Thm3.Prop4
