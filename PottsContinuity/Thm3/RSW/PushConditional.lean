module

public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Exact top-and-sides-wired finite rectangles and the Lemma-3 induction

The finite law and crossing probability of Lemma 3 (top and sides wired), for all
real aspect ratios and natural scales. Lemma 3 itself is
`PottsContinuity.Push.selfDual_push` (`Thm3/Push/UnconditionalPush.lean`).
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- The finite source domain, with the integer floor convention at its sides. -/
noncomputable def topWiredRectangle (k ℓ : ℝ) (n : ℕ) : Finset (ℤ × ℤ) :=
  latticeRectangle (-⌊k * n⌋) ⌊k * n⌋ 0 ⌊ℓ * n⌋

/-- One wired class on the top and the two sides; remaining bottom vertices
are free. At corners the wired condition takes precedence. -/
def topWiredRectangleBoundary (k ℓ : ℝ) (n : ℕ) :
    PD.FK.BoundaryCondition (topWiredRectangle k ℓ n : Set (ℤ × ℤ)) :=
  PD.FK.BoundaryCondition.wired
    {v | v.1.1 = -⌊k * n⌋ ∨ v.1.1 = ⌊k * n⌋ ∨ v.1.2 = ⌊ℓ * n⌋}

/-- Actual horizontal crossing of the height-n subrectangle under the finite
law wired on the domain's other three sides, at the explicit self-dual value. -/
noncomputable def selfDualTopWiredCrossingProbability
    (q : Set.Ici (1 : ℝ)) (k ℓ : ℝ) (n : ℕ) : ℝ :=
  finiteBoundaryEventProbability (topWiredRectangle k ℓ n) (selfDualParameters q)
    (topWiredRectangleBoundary k ℓ n)
    (horizontalCrossing (topWiredRectangle k ℓ n) (-⌊k * n⌋) ⌊k * n⌋ 0 n)

/-- Nonnegativity of the actual finite event probability. -/
theorem selfDualTopWiredCrossingProbability_nonneg
    (q : Set.Ici (1 : ℝ)) (k ℓ : ℝ) (n : ℕ) :
    0 ≤ selfDualTopWiredCrossingProbability q k ℓ n := ENNReal.toReal_nonneg

end PottsContinuity.RSW
