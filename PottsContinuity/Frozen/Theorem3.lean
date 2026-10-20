module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.Theorem3

/-!
# Theorem `theorem_3`

Transcribed from H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1. The
statement was reviewed against the paper and approved by the author before any proof was
written; `Challenge.lean` contains it verbatim. The proof is assembled in
`PottsContinuity.Provider.theorem_3`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- **Theorem 3** (p. 7). Let `q ≥ 1`. The assertions P1–P5 are equivalent (the theorem does not
assert that they hold).  Lattice rounding in P5: `[0,αn] × [0,n]` is the set of lattice points
`{0,…,⌊αn⌋} × {0,…,n}`, whose sides `{0} × [0,n]` and `{αn} × [0,n]` are the columns `x = 0` and
`x = ⌊αn⌋`; `[-n,(α+1)n] × [-n,2n]` is `{-n,…,⌊(α+1)n⌋} × {-n,…,2n}` (note
`⌊(α+1)n⌋ = n + ⌊αn⌋`, so the margin is exactly `n` on every side). -/
theorem theorem_3 (q : ℝ) (hq : 1 ≤ q) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq⟩ pc ∧
      (∀ i, IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq⟩ i (φ i)) ∧
      List.TFAE
        [ -- P1: φ¹_{ℤ²,p_c,q}[0 ⟷ ∞] = 0
          φ 1 {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0,
          -- P2: φ⁰_{ℤ²,p_c,q} = φ¹_{ℤ²,p_c,q}
          φ 0 = φ 1,
          -- P3: χ⁰(p_c, q) = ∑_{x ∈ ℤ²} φ⁰_{ℤ²,p_c,q}[0 ⟷ x] = ∞
          ∑' x : ℤ × ℤ, φ 0 {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ∞,
          -- P4: lim_{n → ∞} (1/n) log φ⁰_{ℤ²,p_c,q}[0 ⟷ ∂Λₙ] = 0
          Tendsto
            (fun n : ℕ => 1 / (n : ℝ) * Real.log ((φ 0).real
              {ω | ∃ y ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
            atTop (𝓝 0),
          -- P5: ∀ α > 0, ∃ c = c(α) > 0, ∀ n ≥ 1,
          --     φ⁰_{[-n,(α+1)n]×[-n,2n],p_c,q}[C_h([0,αn] × [0,n])] ≥ c
          --     (lattice points; `αn` and `(α+1)n` rounded down, see the docstring)
          ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
            c ≤ rcEventProb
              (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
              pc ⟨q, lt_of_lt_of_le one_pos hq⟩ 0
              (horizontalCrossing
                (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
                0 ⌊α * n⌋ 0 n)] :=
  by exact PottsContinuity.Provider.theorem_3

end PottsContinuity
