module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.Theorem1

/-!
# Theorem `theorem_1`

Transcribed from H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1. The
statement was reviewed against the paper and approved by the author before any proof was
written; `Challenge.lean` contains it verbatim. The proof is assembled in
`PottsContinuity.Provider.theorem_1`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- **Theorem 1** (p. 5). Let `q ∈ {2, 3, 4}`. Then for any `i ∈ {1, …, q}`,
`μ^{(i)}_{ℤ², β_c(q)}[σ₀ = i] = 1/q`. -/
theorem theorem_1 (q : ℕ) (hq : q ∈ Set.Icc 2 4) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧ μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) :=
  by exact PottsContinuity.Provider.theorem_1

end PottsContinuity
