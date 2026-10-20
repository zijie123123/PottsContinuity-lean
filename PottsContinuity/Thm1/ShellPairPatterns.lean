module

public import PottsContinuity.Thm1.ShellPairIntersections

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.CorrLength

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Exact finite-shell pair statuses: every pair in `Positive` is wired
together, and every pair in `Negative` is kept separate. -/
def pottsESLatticePairPatternEvent (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Set LatticeConfiguration :=
  pottsESLatticePairIntersectionEvent V Positive \
    (⋃ p ∈ Negative,
      pottsESLatticePairIntersectionEvent V (Positive ∪ {p}))

/-- The corresponding exact pair-status event in the limiting bond measure. -/
def pottsESConnectionPairPatternEvent
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Set LatticeConfiguration :=
  pottsESConnectionIntersectionEvent Positive \
    (⋃ p ∈ Negative,
      pottsESConnectionIntersectionEvent (Positive ∪ {p}))

end

end PottsContinuity.Thm1

