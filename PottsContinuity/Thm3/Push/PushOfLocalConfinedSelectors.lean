module

public import PottsContinuity.Thm3.Push.ConfinedPrefixSelector
public import PottsContinuity.Thm3.Push.PushOfDirectPrefixSystems

@[expose] public section

namespace PottsContinuity.Push
open RSW
noncomputable section

/-- Strip RSW from only existence of a local physical first-contact choice
at each required finite ceiling scale. Source geometry and every numerical
and probabilistic comparison are derived internally. -/
theorem selfDual_stripRSW_of_localConfinedPrefixSelectors
    (q : Set.Ici (1:ℝ))
    (hchoices : ∀ n : ℕ, ∀ hn : 13 ≤ n, RoundedLocalConfinedPrefixSelectorExists n hn) :
    ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualStripHorizontalProbability q K n :=
  selfDual_stripRSW_of_directPrefixSystems q (fun n hn =>
    roundedDirectPrefixSystem_nonempty_of_localConfinedSelector n hn (hchoices n hn))

/-- The exact all-aspect Lemma 3 conclusion from the remaining finite
local-selector existence interface, with no numerical crossing premise. -/
theorem selfDual_push_of_localConfinedPrefixSelectors
    (q : Set.Ici (1:ℝ))
    (hchoices : ∀ n : ℕ, ∀ hn : 13 ≤ n, RoundedLocalConfinedPrefixSelectorExists n hn)
    (k : ℝ) (hk : 0 < k) (ℓ : ℝ) (hℓ : 4/3 ≤ ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualTopWiredCrossingProbability q k ℓ n :=
  selfDual_push_of_stripRSW q (selfDual_stripRSW_of_localConfinedPrefixSelectors q hchoices) k hk ℓ hℓ

end
end PottsContinuity.Push
