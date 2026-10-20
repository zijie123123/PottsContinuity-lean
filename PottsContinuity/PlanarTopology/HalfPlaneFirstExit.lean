module

public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Stop an original open connection at its first vertex in the exterior
column. Every other retained vertex lies in the original right half-plane. -/
theorem open_connection_has_first_exterior_exit (ω : LatticeConfiguration)
    (u v : LatticeVertex) (hu : 0 ≤ u.1) (hv : v.1 ≤ -1)
    (huv : (PD.rcInfiniteOpenGraph ω).Reachable u v) :
    ∃ y : ℤ, ∃ r : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y),
      ∀ z ∈ r.support, 0 ≤ z.1 ∨ z = (-1,y) := by
  obtain ⟨p⟩ := huv
  have hstep : ∀ x y, (PD.rcInfiniteOpenGraph ω).Adj x y → |(-x.1)-(-y.1)| ≤ 1 := by
    intro x y hxy
    have hh := (rcInfiniteOpenGraph_adj ω x y).mp hxy
    have ha := PD.squareLattice.mem_edgeSet.mp hh.1
    change |x.1-y.1|+|x.2-y.2| = 1 at ha
    rw [neg_sub_neg,abs_sub_comm]
    have := abs_nonneg (x.2-y.2)
    omega
  obtain ⟨z,P,Q,hz,he,hP⟩ := walk_prefix_at_level
    (fun x : LatticeVertex => -x.1) hstep p 1 (by omega) (by omega)
  obtain ⟨w,hw,r,s,hrs,hfirst⟩ := walk_first_entry P {x : LatticeVertex | x.1 = -1} (by change z.1 = -1; omega)
  have hrP : r.IsSubwalk P := SimpleGraph.Walk.isSubwalk_of_append_left hrs
  rcases w with ⟨x,y⟩
  change x = -1 at hw
  subst x
  refine ⟨y,r,?_⟩
  intro a ha
  have hb := hP a (hrP.support_subset ha)
  by_cases hax : a.1 = -1
  · right
    exact hfirst a ha hax
  · left
    omega

end
end PottsContinuity.PlanarTopology
