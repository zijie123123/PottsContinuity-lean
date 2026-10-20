module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.IsRCCriticalPointUnique

/-!
# Theorem `isRCCriticalPoint_unique`

Well-definedness of the critical point `p_c(q)` of the random-cluster model (p. 6), which is
implicit in the notation of H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1; it
makes the existential form of the main theorems determine the paper's objects. The statement was
approved by the author before any proof was written; `Challenge.lean` contains it verbatim. The
proof is assembled in `PottsContinuity.Provider.isRCCriticalPoint_unique`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- The critical parameter, when it exists, is unique. -/
theorem isRCCriticalPoint_unique (q : Set.Ici (1 : ℝ)) (a b : ℝ)
    (ha : IsRCCriticalPoint q a) (hb : IsRCCriticalPoint q b) : a = b :=
  by exact PottsContinuity.Provider.isRCCriticalPoint_unique

end PottsContinuity
