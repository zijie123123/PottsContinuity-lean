module

public import PottsContinuity.Thm4.SideBoundary

@[expose] public section

namespace PottsContinuity.Thm4
open Filter Topology
noncomputable section

/-- Removing the two negligible extreme sheets leaves uniformly positive
actual connection mass on interior sheets. -/
theorem cover_side_connection_sum_eventually_lower (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c ≤ ∑ v ∈ coverSideBoundary n, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  obtain ⟨c₀, hc₀, hfull⟩ := cover_boundary_connection_sum_uniform_lower q
  have hsmall : ∀ᶠ n : ℕ in atTop, coverExtremalConnectionMass n q < c₀ / 2 :=
    (tendsto_coverExtremalConnectionMass q).eventually (Iio_mem_nhds (half_pos hc₀))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨c₀ / 2, half_pos hc₀, max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hcap := hN n (le_trans (le_max_right 1 N) hn)
  have hmass := hfull n hn1
  have hsplit := cover_boundary_connection_sum_le_side_add_extremal q n
  linarith

/-- One actual interior-sheet boundary vertex carries polynomially large
connection probability, uniformly for all sufficiently large scales. -/
theorem cover_side_connection_eventual_polynomial_witness (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ v ∈ coverSideBoundary n,
        c / (n : ℝ)^6 ≤ coverOriginConnectionProbability n ⟨q, q.2.1⟩ v := by
  obtain ⟨d, hd, N, hN, hmass⟩ := cover_side_connection_sum_eventually_lower q
  refine ⟨d / 36, by positivity, N, hN, ?_⟩
  intro n hnN
  have hn : 1 ≤ n := le_trans hN hnN
  let S := coverSideBoundary n
  let t : ℝ := (d / 36) / (n : ℝ)^6
  have ht : 0 < t := by dsimp [t]; positivity
  have hsum : d ≤ ∑ v ∈ S, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v :=
    hmass n hnN
  have hcard : (S.card : ℝ) ≤ 36 * (n : ℝ)^6 := by
    exact_mod_cast coverSideBoundary_card_le n hn
  by_contra hnone
  have hlt : ∀ v ∈ S, coverOriginConnectionProbability n ⟨q, q.2.1⟩ v < t := by
    intro v hv
    exact lt_of_not_ge (fun h => hnone ⟨v, hv, h⟩)
  have hsne : S.Nonempty := by
    by_contra he
    have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hEmpty, Finset.sum_empty] at hsum
    linarith
  have hsumlt := Finset.sum_lt_sum_of_nonempty hsne hlt
  have hprod : (S.card : ℝ) * t ≤ d := by
    calc
      _ ≤ (36 * (n : ℝ)^6) * t := mul_le_mul_of_nonneg_right hcard ht.le
      _ = d := by
        dsimp [t]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        field_simp
  have hcst : (∑ _v ∈ S, t) = (S.card : ℝ) * t := by simp
  rw [hcst] at hsumlt
  linarith

end
end PottsContinuity.Thm4
