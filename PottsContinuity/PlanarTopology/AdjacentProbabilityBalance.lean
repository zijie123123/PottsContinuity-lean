module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open Filter Topology

/-- A first threshold crossing supplies adjacent high values. No equality of
the two probabilities, strict sign change, or attained maximum is required. -/
theorem exists_adjacent_above_threshold (A B : ℤ → ℝ) (r : ℝ) (t : ℤ)
    (hA : r < A t) (hB : Monotone B) (hcover : ∀ j, r < max (A j) (B j))
    (hfuture : ∃ n : ℕ, r < B (t+(n : ℤ))) :
    ∃ j : ℤ, r < A j ∧ r < B (j+1) := by
  let n := Nat.find hfuture
  have hn : r < B (t+(n : ℤ)) := Nat.find_spec hfuture
  by_cases hn0 : n = 0
  · refine ⟨t,hA,?_⟩
    have hh : r < B t := by simpa only [hn0,Nat.cast_zero,add_zero] using hn
    exact hh.trans_le (hB (by omega))
  · let p := n-1
    have hp : p < n := by dsimp [p]; omega
    have hnot : ¬ r < B (t+(p : ℤ)) := Nat.find_min hfuture hp
    have hleft : r < A (t+(p : ℤ)) := by
      rcases lt_max_iff.mp (hcover (t+(p : ℤ))) with h | h
      · exact h
      · exact (hnot h).elim
    refine ⟨t+(p : ℤ),hleft,?_⟩
    have he : t+(p : ℤ)+1 = t+(n : ℤ) := by dsimp [p]; omega
    rw [he]
    exact hn

/-- A limiting high value provides the future endpoint of the discrete
balancing argument, for every fixed initial integer location. -/
theorem exists_adjacent_above_threshold_of_tendsto (A B : ℤ → ℝ) (r b : ℝ)
    (hB : Monotone B) (hcover : ∀ j, r < max (A j) (B j))
    (hstart : ∃ t, r < A t) (hlimit : Tendsto B atTop (𝓝 b)) (hrb : r < b) :
    ∃ j : ℤ, r < A j ∧ r < B (j+1) := by
  obtain ⟨t,ht⟩ := hstart
  have he := (tendsto_order.mp hlimit).1 r hrb
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let k := max N t
  have hk : t+(((k-t).toNat : ℕ) : ℤ) = k := by dsimp [k]; omega
  apply exists_adjacent_above_threshold A B r t ht hB hcover
  refine ⟨(k-t).toNat,?_⟩
  rw [hk]
  exact hN k (le_max_left _ _)

end PottsContinuity.PlanarTopology
