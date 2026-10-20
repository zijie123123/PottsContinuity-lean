module

public import PottsContinuity.PlanarMixed.SlitReflectedBonds
public import Mathlib.Tactic

/-! Exact unbounded sampled-bond carriers before and after corrected reflected
duality. The bare reflected sampled carrier is NOT a subgraph of D; a concrete
bond witnesses this. Boundary contraction/deletion must therefore be explicit
in any repaired source domain inclusion. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.Medial

/-- Literal normalized bonds of the upper half-plane slit graph D. -/
def SlitRetainedBond (x y : ℤ) (e : LatticeBond) : Prop :=
  0 ≤ e.base.2 ∧ ¬ (e.axis = .horizontal ∧ e.base.1 = x-1 ∧ y < e.base.2)

end PottsContinuity.PlanarMixed
