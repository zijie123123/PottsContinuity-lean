module

public import PottsContinuity.Thm3.Push.DivisibleProduct
public import PottsContinuity.Thm3.Push.BaseStripComparison
public import PottsContinuity.Thm3.Push.HeightComparison

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW
noncomputable section

/-- The full positive real-height conclusion on divisible scales follows
from the proved highest-frontier product. The only external estimate is
exactly the authorized all-scale Lemma-2 strip-RSW statement. -/
theorem selfDual_divisible_push_of_stripRSW (q : Set.Ici (1 : ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (k : ℝ) (hk : 0 < k) (ℓ : ℝ) (hℓ : 4/3 ≤ ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualTopWiredCrossingProbability q k ℓ (3*s) := by
  obtain ⟨c,hc,hbase⟩ := selfDual_base_at_three_mul_of_stripRSW q hstrip k hk
  have hgrid : ∀ j s : ℕ, 1 ≤ s →
      c^(j+1) ≤ selfDualTopWiredCrossingProbability q k (4/3+j/3) (3*s) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      intro s hs
      calc
        c^(j+1+1) = c^(j+1)*c := pow_succ _ _
        _ ≤ selfDualTopWiredCrossingProbability q k (4/3+j/3) (3*s) *
            selfDualTopWiredCrossingProbability q k (4/3) (3*s) :=
          mul_le_mul (ih s hs) (hbase s hs) hc.le
            (selfDualTopWiredCrossingProbability_nonneg q k _ _)
        _ ≤ selfDualTopWiredCrossingProbability q k (4/3+(j+1 : ℕ)/3) (3*s) := by
          have hj : (4 : ℝ)/3 ≤ 4/3+(j : ℝ)/3 :=
            le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) (by norm_num))
          have hpush := selfDual_push_product_at_three_mul q k hk (4/3+j/3) hj s hs
          simpa only [Nat.cast_add,Nat.cast_one,add_div,add_assoc] using hpush
  obtain ⟨j,hj⟩ := exists_nat_gt (3*ℓ)
  have hle : ℓ ≤ 4/3+(j : ℝ)/3 := by linarith
  refine ⟨c^(j+1),pow_pos hc _,?_⟩
  intro s hs
  exact (hgrid j s hs).trans
    (top_wired_height_comparison q k hk ℓ (4/3+j/3) hℓ hle (3*s) (by omega))

end
end PottsContinuity.Push
