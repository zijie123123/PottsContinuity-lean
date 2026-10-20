module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PlanarMixed.Thm4SideFactor.SideFactor
public import PottsContinuity.Thm4Plane.FinalRootRoutes

/-!
# Proof of `PottsContinuity.theorem_2`

This module proves `PottsContinuity.Provider.theorem_2`, whose statement is exactly that of
`theorem_2` in `Frozen/Theorem2.lean` (with an implicit `q` and an auto-param `hq`), from the
other project modules. The proof in `Frozen/Theorem2.lean` is `by exact` this theorem; no other
module imports this one.

Proof assembly: `Thm4Plane.theorem_2_of_sideFactor` (Theorem 4 at the self-dual point, Theorem 3's
P4 ⇒ P1 chain and p_c = √q/(1+√q)) applied to the Theorem 4 side factor
`PlanarMixed.Thm4SideFactor.slitScreen_sideFactor`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.theorem_2`, with an implicit `q` and an auto-param
`hq`, so that its proof in `Frozen/Theorem2.lean` is `by exact` this theorem. -/
theorem theorem_2 {q : ℝ} (hq : q ∈ Set.Icc (1 : ℝ) 4 := by assumption) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
      IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
      φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 :=
  Thm4Plane.theorem_2_of_sideFactor q hq (PlanarMixed.Thm4SideFactor.slitScreen_sideFactor q hq)

end PottsContinuity.Provider
