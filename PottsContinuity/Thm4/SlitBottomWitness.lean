module

public import PottsContinuity.Thm4.SlitComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK MeasureTheory
noncomputable section

/-- The one-scale bottom-center connection event is nonempty and has positive
probability for every real q>=1, under the actual slit-box measure. -/
theorem slit_bottom_center_probability_pos_one (q : Set.Ici (1 : ℝ)) :
    0 < slitArcConnectionProbability 1 q
      (PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex 1) := by
  let q₁ : PottsContinuity.FKC.ClusterWeight := ⟨1, by norm_num⟩
  have hbound :=
    PottsContinuity.FKC.FiniteFK.slitBox_bottom_center_arc_hit_probability_lower_bound_at_one q₁
  have hp : 0 < (1 / (1 + PottsContinuity.FKC.loopWeight q₁) : ℝ) :=
    div_pos (by norm_num) (PottsContinuity.FKC.one_add_loopWeight_pos q₁)
  have h := hp.trans_le hbound
  rw [fkc_measure_eq] at h
  have hpos := (ENNReal.toReal_pos_iff.mp h).1
  have hne := (measure_pos_iff (PottsContinuity.FKC.FiniteFK.slitBoxGraph 1)
    (selfDualParameters ⟨q₁, q₁.2.1⟩)
    (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary 1))
    (PottsContinuity.FKC.FiniteFK.slitBoxWiredArcConnectionEvent 1
      (PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex 1))).mp hpos
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((measure_pos_iff (PottsContinuity.FKC.FiniteFK.slitBoxGraph 1)
      (selfDualParameters q)
      (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary 1)) _).mpr hne)
  · exact measure_ne_top _ _

/-- At every scale, some actual bottom vertex in the slit box has at least a
polynomial connection probability to the wired arc, for all real 1<=q<=4.
The law is at the explicit self-dual value. -/
theorem slit_bottom_arc_polynomial_witness (q : Set.Icc (1 : ℝ) 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ u : PottsContinuity.FKC.FiniteFK.SlitBoxVertex m,
        u.val.2 = -(m : ℤ) ∧
        c / (m : ℝ)^6 ≤ slitArcConnectionProbability m ⟨q, q.2.1⟩ u := by
  obtain ⟨c₀, hc₀, hcover⟩ := cover_side_connection_polynomial_witness q
  let p₁ := slitArcConnectionProbability 1 ⟨q, q.2.1⟩
    (PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex 1)
  let c := min p₁ (c₀ / 27)
  have hc : 0 < c := lt_min (slit_bottom_center_probability_pos_one _) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    refine ⟨PottsContinuity.FKC.FiniteFK.slitBoxBottomCenterVertex 1, ?_, ?_⟩
    · simp
    · simpa only [Nat.cast_one, one_pow, div_one] using (min_le_left p₁ (c₀ / 27))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    obtain ⟨v, hv, hbound⟩ := hcover n hn
    obtain ⟨u, hu, hside⟩ := cover_side_to_slit n hn q v hv
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hpow : (n : ℝ)^6 ≤ ((n + 1 : ℕ) : ℝ)^6 :=
      pow_le_pow_left₀ hnR.le (by norm_cast; omega) 6
    have hden : 0 < ((n + 1 : ℕ) : ℝ)^6 := by positivity
    refine ⟨u, hu, ?_⟩
    calc
      c / ((n + 1 : ℕ) : ℝ)^6 ≤ (c₀ / 27) / ((n + 1 : ℕ) : ℝ)^6 :=
        div_le_div_of_nonneg_right (min_le_right _ _) hden.le
      _ ≤ (c₀ / 27) / (n : ℝ)^6 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hnR _) hpow
      _ = (1 / 27 : ℝ) * (c₀ / (n : ℝ)^6) := by ring
      _ ≤ (1 / 27 : ℝ) * coverOriginConnectionProbability n ⟨q, q.2.1⟩ v :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ ≤ slitArcConnectionProbability (n + 1) ⟨q, q.2.1⟩ u := hside

end
end PottsContinuity.Thm4
