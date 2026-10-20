module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.IsPottsCriticalPointUnique

/-!
# Theorem `isPottsCriticalPoint_unique`

Well-definedness of the critical inverse temperature `β_c(q)` of the Potts model (p. 4), which is
implicit in the notation of H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1; it
makes the existential form of the main theorems determine the paper's objects. The statement was
approved by the author before any proof was written; `Challenge.lean` contains it verbatim. The
proof is assembled in `PottsContinuity.Provider.isPottsCriticalPoint_unique`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- Well-definedness of `β_c(q)`: the critical inverse temperature is unique (q ≥ 2). -/
theorem isPottsCriticalPoint_unique (q : ℕ) (hq : 2 ≤ q) (βc βc' : ℝ)
    (h : IsPottsCriticalPoint q βc) (h' : IsPottsCriticalPoint q βc') : βc = βc' :=
  by exact PottsContinuity.Provider.isPottsCriticalPoint_unique

end PottsContinuity
