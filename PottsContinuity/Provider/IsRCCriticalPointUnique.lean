module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.WellDefined.Uniqueness

/-!
# Proof of `PottsContinuity.isRCCriticalPoint_unique`

This module proves `PottsContinuity.Provider.isRCCriticalPoint_unique`, whose statement is exactly
that of `isRCCriticalPoint_unique` in `Frozen/IsRCCriticalPointUnique.lean` (with implicit binders
and auto-param hypotheses), by `WellDefined.criticalPoint_unique`. The proof in
`Frozen/IsRCCriticalPointUnique.lean` is `by exact` this theorem; no other module imports this one.
-/

@[expose] public section

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.isRCCriticalPoint_unique`, with implicit binders and
auto-param hypotheses, so that its proof in `Frozen/IsRCCriticalPointUnique.lean` is `by exact` this
theorem. -/
theorem isRCCriticalPoint_unique {q : Set.Ici (1 : ℝ)} {a b : ℝ}
    (ha : IsRCCriticalPoint q a := by assumption)
    (hb : IsRCCriticalPoint q b := by assumption) : a = b :=
  WellDefined.criticalPoint_unique q a b ha hb

end PottsContinuity.Provider
