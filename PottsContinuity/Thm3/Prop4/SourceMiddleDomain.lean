module

public import PottsContinuity.Thm3.Prop4.LowerTraceHull
public import PottsContinuity.BD12.RectangleOpenGraphs

/-!
# The source middle domain defined by access avoiding the two traces

Vertices on either trace are retained. Away from both traces the domain
consists of vertices with top access avoiding the lower trace and bottom
access avoiding the upper trace. Interior adjacency preserves both accesses.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- Bottom-row access inside the original box, avoiding the indicated trace. -/
def traceBottomAccessible (n : ℕ) (trace : Finset LatticeVertex) (x : LatticeVertex) : Prop :=
  ∃ t : LatticeVertex, t.2 = -(n : ℤ) ∧
    ∃ p : PD.squareLattice.Walk x t, ∀ z ∈ p.support, z ∈ box n ∧ z ∉ trace

/-- The trace-supported middle domain, on the actual original box carrier. -/
def sourceMiddleDomain (n : ℕ) (lower upper : Finset LatticeVertex) :
    Set (box n : Set LatticeVertex) :=
  {x | x.val ∈ lower ∪ upper ∨
    traceTopAccessible n lower x.val ∧ traceBottomAccessible n upper x.val}

end
end PottsContinuity.Thm3.Prop4
