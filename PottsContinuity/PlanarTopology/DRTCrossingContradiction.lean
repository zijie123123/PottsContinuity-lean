module

public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PottsContinuity.PlanarTopology
open Filter Topology

/-- At consecutive balanced heights, the source's large maximum equals the
maximum of the two small crossing minima. -/
theorem balanced_crossing_max_eq (h v h' v' : ℝ) (hbalance : h ≤ v) (hbalance' : v' ≤ h') :
    max h v' = max (min v h) (min v' h') := by
  rw [min_eq_right hbalance,min_eq_left hbalance']

/-- The two crossing limits in DRT cannot hold at consecutive balanced heights.
This is the final scalar contradiction, with the geometric limits explicit. -/
theorem drt_crossing_contradiction_of_crossingLimits
    (h v : ℕ → ℕ → ℝ) (k : ℕ → ℕ)
    (hbalance : ∀ n, h n (k n) ≤ v n (k n))
    (hbalance' : ∀ n, v n (k n+1) ≤ h n (k n+1))
    (hlarge : Tendsto (fun n => max (h n (k n)) (v n (k n+1))) atTop (𝓝 1))
    (hsmall : Tendsto (fun n => min (v n (k n)) (h n (k n))) atTop (𝓝 0))
    (hsmall' : Tendsto (fun n => min (v n (k n+1)) (h n (k n+1))) atTop (𝓝 0)) : False := by
  have hzero : Tendsto (fun n => max (h n (k n)) (v n (k n+1))) atTop (𝓝 0) := by
    have hh := hsmall.max hsmall'
    simpa only [max_self,← balanced_crossing_max_eq _ _ _ _ (hbalance _) (hbalance' _)] using hh
  have hh : (1 : ℝ) = 0 := tendsto_nhds_unique hlarge hzero
  norm_num at hh

end PottsContinuity.PlanarTopology
