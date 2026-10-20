module

public import PottsContinuity.Thm3.RSW.PairScaleInterpolation
public import PottsContinuity.Thm3.RSW.PairStrict
public import PottsContinuity.Thm3.RSW.ArmStrict
public import PottsContinuity.Thm3.RSW.StretchedRate
public import PottsContinuity.Thm3.RSW.SquarePairDecay

/-!
# The corrected Proposition-3 consumer

The annulus recurrence (Lemma 4) and reflected-FKG circuit construction remain
explicit interfaces; the integral gluing power is arbitrary and positive,
avoiding the source's reviewed 7-versus-15 factor discrepancy. All selection of scales, interpolation, weighted tails,
finite-energy strictness and removal of prefactors are proved here. No theorem
in this file is an unconditional export of Proposition 3.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology

/-- The two remaining geometric inputs give all-scale pair decay, with the
source exponent and a positive rate adjusted at finitely many small scales. -/
theorem squarePair_stretched_decay_of_induction1_reflectedFKG
    (q : Set.Ici (1:ℝ)) (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (hp : 0 < p)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hreflectedFKG : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → n ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 n)
    (hfail : ¬ ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n) :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, 1 ≤ m →
      maxSquarePairProbability (selfDualParameters q) m ≤
        Real.exp (-d*(m:ℝ)^sevenfoldExponent) := by
  obtain ⟨n₀, hn₀, d, hd, hladder⟩ :=
    selfDual_annulus_ladder_decay_of_induction1 q C (zero_lt_one.trans_le hC) hinduction1 hfail
  have htail := squarePair_eventual_decay_of_reflectedFKG q C d hC hd n₀ hn₀ p hp hladder
    (fun k m hm hmn hnm => hreflectedFKG _ m
      (hn₀.trans (Nat.le_mul_of_pos_left n₀ (pow_pos (by decide) k))) hm hmn hnm)
  apply stretched_bound_all_positive_of_eventually
    (maxSquarePairProbability (selfDualParameters q)) (d/(p:ℝ)) sevenfoldExponent
    (div_pos hd (by exact_mod_cast hp)) sevenfoldExponent_lt_one.le
    (maxSquarePairProbability_lt_one (selfDualParameters q))
  exact eventually_atTop.mpr ⟨n₀, htail⟩

/-- The corrected all-positive-scale arm alternative, conditional only on the
explicit annulus recurrence and reflected-FKG construction. The prefactor in
the weighted-tail bound is removed using proved free-arm finite energy. -/
theorem selfDual_oneArm_stretched_decay_of_induction1_reflectedFKG
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (hp : 0 < p)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hreflectedFKG : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → n ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 n)
    (hfail : ¬ ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → oneArmProbability μ n ≤
      Real.exp (-c*(n:ℝ)^sevenfoldExponent) := by
  obtain ⟨d, hd, hpair⟩ :=
    squarePair_stretched_decay_of_induction1_reflectedFKG q C hC p hp hinduction1 hreflectedFKG hfail
  obtain ⟨K, hK, harm⟩ := oneArm_stretched_bound_of_squarePairDecay
    (selfDualParameters q) μ hμ d sevenfoldExponent hd sevenfoldExponent_pos hpair
  exact stretched_bound_all_positive_of_prefactor (oneArmProbability μ) K (d/2)
    sevenfoldExponent hK (half_pos hd) sevenfoldExponent_pos sevenfoldExponent_lt_one.le
    (oneArmProbability_lt_one (selfDualParameters q) μ hμ) harm

/-- The at-least-one alternative needed by the P4 assembly. The two geometric
inputs are visible. Mutual exclusion is not asserted by this helper. -/
theorem selfDual_dualityP_corrected_of_induction1_reflectedFKG
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (hp : 0 < p)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hreflectedFKG : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → n ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 n) :
    (∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n → a ≤ annulusProbability (selfDualParameters q) 8 n) ∨
    (∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
      oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)^β)) := by
  classical
  by_cases hfirst : ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n
  · exact Or.inl hfirst
  · obtain ⟨c, hc, hdecay⟩ := selfDual_oneArm_stretched_decay_of_induction1_reflectedFKG
      q μ hμ C hC p hp hinduction1 hreflectedFKG hfirst
    exact Or.inr ⟨c, sevenfoldExponent, hc, sevenfoldExponent_pos, hdecay⟩

end PottsContinuity.RSW
