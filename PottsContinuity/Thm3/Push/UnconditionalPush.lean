module

public import PottsContinuity.Thm3.Push.PushOfLocalConfinedSelectors
public import PottsContinuity.PlanarMixed.StripRSWSelectors.RoundedLocalSelector

@[expose] public section

namespace PottsContinuity.Push
open RSW
noncomputable section

/-- Lemma 3 at the explicit self-dual parameter with its exact all-aspect
conclusion and a positive constant independent of the scale. -/
theorem selfDual_push (q : Set.Ici (1:ℝ))
    (k : ℝ) (hk : 0 < k) (ℓ : ℝ) (hℓ : 4/3 ≤ ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualTopWiredCrossingProbability q k ℓ n :=
  selfDual_push_of_localConfinedPrefixSelectors q
    PlanarMixed.StripRSWSelectors.roundedLocalConfinedPrefixSelectorExists k hk ℓ hℓ

end
end PottsContinuity.Push
