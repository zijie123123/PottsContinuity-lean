module

public import PottsContinuity.Thm1.Theorem1Conditional
public import PottsContinuity.Thm1.PottsInfiniteLimit
public import PottsContinuity.Thm1.PottsInfiniteMagnetisation

/-!
# Theorem 1 from Theorem 2

The infinite-volume Potts measures exist for every `β ≥ 0`, and the corrected Edwards–Sokal identity
`μ[σ₀ = i] = 1/q + (1 − 1/q) φ¹[0 ⟷ ∞]` holds for them. With the value of `p_c` this identifies
`β_c = log (1 + √q)` and reduces Theorem 1 to Theorem 2.
-/

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity

noncomputable section

/-- The critical inverse temperature of the q-state Potts model is `log (1 + √q)` for every
`q ≥ 2`: the transfer `isPottsCriticalPoint_log_sqrt_of_limit_magnetisation` with its two
hypotheses discharged by `exists_isPottsInfiniteVolumeLimit` and
`pottsInfiniteLimit_magnetisation_identity_all`. -/
theorem isPottsCriticalPoint_log_sqrt (q : ℕ) (hq : 2 ≤ q) :
    IsPottsCriticalPoint q (Real.log (1 + Real.sqrt (q : ℝ))) :=
  isPottsCriticalPoint_log_sqrt_of_limit_magnetisation q hq
    (fun β i => exists_isPottsInfiniteVolumeLimit q (by omega) β β.property i)
    (fun β i μ hμ ν hν =>
      pottsInfiniteLimit_magnetisation_identity_all q (by omega) β i μ hμ ν hν)

/-- Theorem 1 from Theorem 2, through the Edwards–Sokal coupling. -/
theorem theorem_1_of_theorem2
    (hTheorem2 : ∀ (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4),
      ∃ (pc : Set.Icc (0 : ℝ) 1)
        (φ₁ : Measure (squareLattice.edgeSet → Bool)),
        IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
          IsRCInfiniteVolumeLimit pc
            ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
          φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0)
    (q : ℕ) (hq : q ∈ Set.Icc 2 4) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧
          μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) := by
  exact theorem_1_of_theorem2_of_limit_magnetisation
    (fun q β i => by
      have hqpos : 0 < q := Nat.pos_of_ne_zero (by
        intro hzero
        subst q
        exact Fin.elim0 i)
      exact exists_isPottsInfiniteVolumeLimit q (by omega) β β.property i)
    (fun q hq β i μ hμ ν hν =>
      pottsInfiniteLimit_magnetisation_identity_all q hq β i μ hμ ν hν)
    hTheorem2 q hq

end

end PottsContinuity.Thm1
