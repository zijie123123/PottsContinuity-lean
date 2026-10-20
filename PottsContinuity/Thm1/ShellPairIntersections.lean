module

public import PottsContinuity.Thm1.ShellPairEvent
public import PottsContinuity.Thm1.ShellBondLimit
public import PottsContinuity.PD.RCInfinite.BurtonKeane
public import PottsContinuity.PD.CorrLength.ConnectionEvents

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

/-- Simultaneous finite-shell relations on a finite family of site pairs. -/
def pottsESLatticePairIntersectionEvent (V : Finset (ℤ × ℤ))
    (P : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Set LatticeConfiguration :=
  ⋂ p ∈ P, pottsESLatticePairRelationEvent V p.1 p.2

/-- Simultaneous whole-lattice connections for a finite family of site pairs. -/
def pottsESConnectionIntersectionEvent
    (P : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Set LatticeConfiguration :=
  ⋂ p ∈ P, connectionEvent p.1 p.2

end

end PottsContinuity.Thm1

