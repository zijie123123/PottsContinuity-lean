module

public import PottsContinuity.Thm3.RSW.Lemma4SideReferencePositive
public import PottsContinuity.Thm3.Push.PushOfStripRSW

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- The side-reference probabilities have a uniform positive lower bound
once the explicit finite dual comparison with a padded Lemma3 rectangle is
supplied. Scale one uses its proved original sampled witness. -/
theorem selfDual_lemma4SideReference_lower_of_dualPushComparison_and_stripRSW
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (hdualPushComparison : ∀ n : ℕ, 2 ≤ n → ∀ i : Fin 2,
      selfDualTopWiredCrossingProbability q 180 180 (n/2) ≤
        lemma4SideReferenceProbability (selfDualParameters q) n i) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ i : Fin 2,
      c ≤ lemma4SideReferenceProbability (selfDualParameters q) n i := by
  obtain ⟨a,ha,hpush⟩ := Push.selfDual_push_of_stripRSW q hstrip 180 (by norm_num)
    180 (by norm_num)
  let d := min (lemma4SideReferenceProbability (selfDualParameters q) 1 0)
    (lemma4SideReferenceProbability (selfDualParameters q) 1 1)
  have hd : 0 < d := lt_min
    (lemma4SideReferenceProbability_pos _ 1 (by omega) 0)
    (lemma4SideReferenceProbability_pos _ 1 (by omega) 1)
  refine ⟨min a d,lt_min ha hd,?_⟩
  intro n hn i
  by_cases hn₂ : 2 ≤ n
  · exact (min_le_left a d).trans ((hpush (n/2) (by omega)).trans (hdualPushComparison n hn₂ i))
  · have hn₁ : n = 1 := by omega
    subst n
    apply (min_le_right a d).trans
    exact Fin.cases (min_le_left _ _) (fun _ => min_le_right _ _) i

end PottsContinuity.RSW
