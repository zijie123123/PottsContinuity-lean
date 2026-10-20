module

public import PottsContinuity.Thm3.RSW.StripLimit
public import PottsContinuity.PD.Duality.FiniteDuality

/-!
# The explicit self-dual parameter and its constructed strip law

All subsequent §3.3 parameter specializations use the formula sqrt(q)/(1+sqrt(q)).
Identifying a genuine percolation threshold is outside these declarations.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.RSW

/-- Interior FK parameters at the explicit self-dual value, for all real q≥1. -/
noncomputable def selfDualParameters (q : Set.Ici (1 : ℝ)) : PD.FK.Parameters :=
  PD.FK.criticalParameters q

/-- Dualizing the explicit parameter record leaves it unchanged. -/
theorem selfDualParameters_fixed (q : Set.Ici (1 : ℝ)) :
    PD.Duality.dualParameters (selfDualParameters q) = selfDualParameters q :=
  PD.FK.dualParameters_criticalParameters q

/-- The unique top-only strip cylinder law at the explicit self-dual value.
The selected object has already been proved to exist uniquely. -/
noncomputable def selfDualStripMeasure (q : Set.Ici (1 : ℝ)) (n : ℕ) :
    Measure (StripConfiguration n) :=
  (isTopWiredStripLimit_top_existsUnique (selfDualParameters q) n).choose

/-- The selected law satisfies the actual strip cylinder-limit predicate. -/
theorem selfDualStripMeasure_isLimit (q : Set.Ici (1 : ℝ)) (n : ℕ) :
    IsTopWiredStripLimit (selfDualParameters q) n 0 (selfDualStripMeasure q n) :=
  (isTopWiredStripLimit_top_existsUnique (selfDualParameters q) n).choose_spec.1

/-- The constructed strip law is a genuine probability measure. -/
instance selfDualStripMeasure_isProbabilityMeasure (q : Set.Ici (1 : ℝ)) (n : ℕ) :
    IsProbabilityMeasure (selfDualStripMeasure q n) :=
  (selfDualStripMeasure_isLimit q n).1

/-- Actual open edges on the infinite strip, without virtual wired paths. -/
def stripOpenGraph (n : ℕ) (ω : StripConfiguration n) : SimpleGraph (stripVertices n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ (stripGraph n).edgeSet, ω ⟨e, h⟩ = true}

/-- A horizontal strip crossing confined to the specified integer rectangle. -/
def stripHorizontalCrossing (n : ℕ) (a b c d : ℤ) : Set (StripConfiguration n) :=
  {ω | ∃ (x y : stripVertices n) (w : (stripOpenGraph n ω).Walk x y),
    x.1 ∈ ({a} : Set ℤ) ×ˢ Set.Icc c d ∧ y.1 ∈ ({b} : Set ℤ) ×ˢ Set.Icc c d ∧
      ∀ v ∈ w.support, v.1 ∈ Set.Icc a b ×ˢ Set.Icc c d}

/-- The Lemma-2 crossing probability at the explicit self-dual parameter.
Both horizontal endpoints use the lattice-point convention. -/
noncomputable def selfDualStripHorizontalProbability (q : Set.Ici (1 : ℝ))
    (k : ℝ) (n : ℕ) : ℝ :=
  (selfDualStripMeasure q n).real
    (stripHorizontalCrossing n (-⌊k * n⌋) ⌊k * n⌋ 0 (2 * n))

end PottsContinuity.RSW
