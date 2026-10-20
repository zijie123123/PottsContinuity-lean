module

public import PottsContinuity.Thm3.Prop4.MarkedBoxTraceNonempty
public import PottsContinuity.Thm3.Prop4.MarkedUpperRawAccess
public import PottsContinuity.Thm3.Prop4.SourceMiddleDomain

/-! # Actual source trace access barriers for the unchanged raw record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance rawMarkedTraceAccessEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Lower raw queries have no top access avoiding the SAME existing lower
source trace, on every genuine connection without a nonemptiness input. -/
theorem markedLowerBoxRawReveal_endpoint_no_top_access_of_connection
    (n : ℕ) (hn : 1 ≤ n) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (e : (finiteLatticeGraph (box n)).edgeSet) (he : e ∈ markedLowerBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) :
    ¬traceTopAccessible n ((markedLowerBoxTrace n u v A).image Subtype.val) x.val :=
  markedLowerBoxRawReveal_endpoint_no_top_access n u v hu hv A
    (markedLowerBoxTrace_nonempty_of_marked_connection n hn u v hu hv A hA) e he x hx

/-- Upper raw queries have no bottom access avoiding the SAME existing
upper source trace, on every genuine connection. -/
theorem markedUpperBoxRawReveal_endpoint_no_bottom_access_of_connection
    (n : ℕ) (hn : 1 ≤ n) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (e : (finiteLatticeGraph (box n)).edgeSet) (he : e ∈ markedUpperBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) :
    ¬traceBottomAccessible n ((markedUpperBoxTrace n u v A).image Subtype.val) x.val :=
  markedUpperBoxRawReveal_endpoint_no_bottom_access n u v hu hv A
    (markedUpperBoxTrace_nonempty_of_marked_connection n hn u v hu hv A hA) e he x hx

end
end PottsContinuity.Thm3.Prop4
