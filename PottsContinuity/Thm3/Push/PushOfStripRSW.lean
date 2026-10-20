module

public import PottsContinuity.Thm3.Push.DivisibleHeightInduction
public import PottsContinuity.Thm3.Push.AllScaleTransfer

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW
noncomputable section

/-- Lemma 3 at the explicit self-dual parameter for every real q>=1, with
Lemma 2 (strip RSW, `hstrip`) as its ONLY hypothesis. The base comparison,
highest-frontier product, stopped-law/locality and random-domain inputs,
height induction, all-scale rounding and finite-scale positivity are proved.

In the induction step ℓ → ℓ + 1/3 of Lemma 3, the product is used at n=3*s; then
`Push.AllScaleTransfer` and finite positivity recover every n>=1. -/
theorem selfDual_push_of_stripRSW (q : Set.Ici (1 : ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (k : ℝ) (hk : 0 < k) (ℓ : ℝ) (hℓ : 4/3 ≤ ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualTopWiredCrossingProbability q k ℓ n := by
  apply selfDual_all_scale_bound_of_divisible_bound q k ℓ hk hℓ
  exact selfDual_divisible_push_of_stripRSW q hstrip (2*k) (by linarith) (2*ℓ) (by linarith)

end
end PottsContinuity.Push
