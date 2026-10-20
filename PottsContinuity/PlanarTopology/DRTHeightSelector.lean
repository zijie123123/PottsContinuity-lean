module

public import PottsContinuity.PlanarTopology.DRTCrossingContradiction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open Filter Topology

/-- The first strict crossing of two height profiles gives consecutive
balanced heights, without assuming continuity or equality at an integer. -/
theorem exists_balanced_consecutive_height (h v : ℕ → ℝ)
    (hzero : h 0 ≤ v 0) (hcross : ∃ N, v N < h N) :
    ∃ k, h k ≤ v k ∧ v (k+1) < h (k+1) := by
  classical
  have hpos : 0 < Nat.find hcross := by
    by_contra hn
    have he : Nat.find hcross = 0 := by omega
    have hh := Nat.find_spec hcross
    rw [he] at hh
    linarith
  refine ⟨Nat.find hcross-1,?_,?_⟩
  · have hh := Nat.find_min hcross (show Nat.find hcross-1 < Nat.find hcross by omega)
    exact le_of_not_gt hh
  · have he : Nat.find hcross-1+1 = Nat.find hcross := by omega
    rw [he]
    exact Nat.find_spec hcross

/-- Fixed-height limits force the consecutive balancing heights to infinity.
The hypotheses concern numerical profiles; rectangle geometry is kept explicit. -/
theorem exists_balanced_height_tendsto_atTop_of_fixedHeightLimits
    (h v : ℕ → ℕ → ℝ)
    (hmono : ∀ n, Monotone (h n)) (vanti : ∀ n, Antitone (v n))
    (hzero : ∀ n, h n 0 ≤ v n 0) (hcross : ∀ n, ∃ N, v n N < h n N)
    (hfixed : ∀ K, Tendsto (fun n => h n K) atTop (𝓝 0))
    (vfixed : ∀ K, Tendsto (fun n => v n K) atTop (𝓝 1)) :
    ∃ k : ℕ → ℕ, (∀ n, h n (k n) ≤ v n (k n) ∧ v n (k n+1) < h n (k n+1)) ∧
      Tendsto k atTop atTop := by
  classical
  choose k hk using fun n => exists_balanced_consecutive_height (h n) (v n) (hzero n) (hcross n)
  refine ⟨k,hk,tendsto_atTop.mpr ?_⟩
  intro K
  have hh := (tendsto_order.mp (hfixed K)).2 (1/2) (by norm_num : (0 : ℝ) < 1/2)
  have hv := (tendsto_order.mp (vfixed K)).1 (1/2) (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [hh,hv] with n hn vn
  by_contra hkn
  have hkn' : k n+1 ≤ K := by omega
  have ha := hmono n hkn'
  have hb := vanti n hkn'
  have hc := (hk n).2
  linarith

end PottsContinuity.PlanarTopology
