module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Thm1.Uniqueness

/-!
# Proof of `PottsContinuity.isPottsCriticalPoint_unique`

This module proves `PottsContinuity.Provider.isPottsCriticalPoint_unique`, whose statement is
exactly that of `isPottsCriticalPoint_unique` in `Frozen/IsPottsCriticalPointUnique.lean` (with
implicit binders and auto-param hypotheses), by `Thm1.potts_criticalPoint_unique`. The proof in
`Frozen/IsPottsCriticalPointUnique.lean` is `by exact` this theorem; no other module imports this
one.
-/

@[expose] public section

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.isPottsCriticalPoint_unique`, with implicit binders
and auto-param hypotheses, so that its proof in `Frozen/IsPottsCriticalPointUnique.lean` is
`by exact` this theorem. -/
theorem isPottsCriticalPoint_unique {q : ℕ} (hq : 2 ≤ q := by assumption) {βc βc' : ℝ}
    (h : IsPottsCriticalPoint q βc := by assumption)
    (h' : IsPottsCriticalPoint q βc' := by assumption) : βc = βc' :=
  Thm1.potts_criticalPoint_unique q hq βc βc' h h'

end PottsContinuity.Provider
