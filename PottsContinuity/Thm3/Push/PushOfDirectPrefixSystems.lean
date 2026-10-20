module

public import PottsContinuity.Thm3.Push.DirectPrefixRoundedLocal
public import PottsContinuity.Thm3.Push.PushOfStripRSW
public import PottsContinuity.Thm3.RSW.StripRSWFromThirteen

@[expose] public section

namespace PottsContinuity.Push
open RSW
noncomputable section

/-- Physical rounded direct-prefix systems supply all-scale real-aspect
strip RSW. Finite gluing, the two source alternatives, dual reflection,
small scales, and the real-aspect passage are discharged. -/
theorem selfDual_stripRSW_of_directPrefixSystems
    (q : Set.Ici (1:ℝ))
    (hsystems : ∀ n : ℕ, ∀ hn : 13 ≤ n, Nonempty (RoundedDirectPrefixSystem n hn)) :
    ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualStripHorizontalProbability q K n := by
  apply selfDual_stripRSW_real_aspect_all_scales_of_rounded_local_connections_from_thirteen q
  intro k hk n hn hsmall j
  obtain ⟨D⟩ := hsystems n hn
  exact directPrefixSystem_rounded_local_of_small_horizontal q n k hn hk D hsmall
    (stripConnectionShift k ((n+8)/9) j)

end
end PottsContinuity.Push
