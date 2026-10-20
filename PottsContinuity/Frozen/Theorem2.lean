module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.Theorem2

/-!
# Theorem `theorem_2`

Transcribed from H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1. The
statement was reviewed against the paper and approved by the author before any proof was
written; `Challenge.lean` contains it verbatim. The proof is assembled in
`PottsContinuity.Provider.theorem_2`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- **Theorem 2** (p. 6). Let `q ∈ [1, 4]`; then `φ¹_{ℤ², p_c(q), q}[0 ⟷ ∞] = 0`. -/
theorem theorem_2 (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
      IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
      φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 :=
  by exact PottsContinuity.Provider.theorem_2

end PottsContinuity
