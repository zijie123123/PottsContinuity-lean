module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.IsRCInfiniteVolumeLimitUnique

/-!
# Theorem `isRCInfiniteVolumeLimit_unique`

Well-definedness of the infinite-volume random-cluster measures `φ^0`, `φ^1` (pp. 5–6), which is
implicit in the notation of H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1; it
makes the existential form of the main theorems determine the paper's objects. The statement was
approved by the author before any proof was written; `Challenge.lean` contains it verbatim. The
proof is assembled in `PottsContinuity.Provider.isRCInfiniteVolumeLimit_unique`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- The infinite-volume limit, when it exists, is unique. -/
theorem isRCInfiniteVolumeLimit_unique (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (μ ν : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) (hν : IsRCInfiniteVolumeLimit p q i ν) :
    μ = ν :=
  by exact PottsContinuity.Provider.isRCInfiniteVolumeLimit_unique

end PottsContinuity
