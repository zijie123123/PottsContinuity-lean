module

public import PottsContinuity.Thm3.RSW.StripRoundedGluing
public import PottsContinuity.Thm3.RSW.StripFiniteScaleUniform

/-! # Rounded local estimates above the source-rectangle containment cutoff -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Rounded local connections above the source containment cutoff give a uniform bound.
Their local exploration estimate remains explicit; finite FKG and all
translated-path geometry are supplied by the proved strip library. -/
theorem selfDual_stripRSW_large_scales_of_rounded_local_connections_from_thirteen
    (q : Set.Ici (1:ℝ)) (k : ℕ) (hk : 1 ≤ k)
    (hlocal : ∀ n : ℕ, 13 ≤ n →
      selfDualStripHorizontalProbability q k n < 1/2 →
      ∀ j : Fin (18*k), stripLocalLower q k ≤
        (selfDualStripMeasure q n).real
          (stripLocalConnection n ((n+8)/9)
            (stripConnectionShift k ((n+8)/9) j))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 13 ≤ n →
      c ≤ selfDualStripHorizontalProbability q k n := by
  classical
  let b := stripLocalLower q k
  have hb : 0 < b := stripLocalLower_pos q k hk
  refine ⟨min (1/2) (b^(18*k)),lt_min (by norm_num) (pow_pos hb _),?_⟩
  intro n hn
  by_cases hlarge : 1/2 ≤ selfDualStripHorizontalProbability q k n
  · exact (min_le_left _ _).trans hlarge
  · have hs := strip_ceil_ninth_spacing n (by omega)
    have hglue := strip_translated_connections_glue_of_scale_le k hk n ((n+8)/9) hs.1 hs.2.1
    have hsmall := lt_of_not_ge hlarge
    have hlower := selfDual_strip_crossing_lower_of_finite_gluing q n k
      (Finset.univ : Finset (Fin (18*k)))
      (fun j => stripLocalConnection n ((n+8)/9)
        (stripConnectionShift k ((n+8)/9) j)) b hb.le
      (fun _ _ => stripConfinedConnection_isClopen _ _ _ _)
      (fun _ _ => stripConfinedConnection_isUpperSet _ _ _ _)
      (fun j _ => hlocal n hn hsmall j) (by simpa using hglue)
    have hcard : (Finset.univ : Finset (Fin (18*k))).card = 18*k := by simp
    rw [hcard] at hlower
    exact (min_le_right _ _).trans hlower

/-- All scales below13 are absorbed using actual strict
positivity. Thus no extra small-scale or divisibility premise remains. -/
theorem selfDual_stripRSW_all_scales_of_rounded_local_connections_from_thirteen
    (q : Set.Ici (1:ℝ)) (k : ℕ) (hk : 1 ≤ k)
    (hlocal : ∀ n : ℕ, 13 ≤ n →
      selfDualStripHorizontalProbability q k n < 1/2 →
      ∀ j : Fin (18*k), stripLocalLower q k ≤
        (selfDualStripMeasure q n).real
          (stripLocalConnection n ((n+8)/9)
            (stripConnectionShift k ((n+8)/9) j))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualStripHorizontalProbability q k n := by
  obtain ⟨c₁,hc₁,hlarge⟩ :=
    selfDual_stripRSW_large_scales_of_rounded_local_connections_from_thirteen q k hk hlocal
  obtain ⟨c₂,hc₂,hsmall⟩ := selfDual_strip_crossing_finite_scales_uniform_pos
    q k (Nat.cast_nonneg k) 12
  refine ⟨min c₁ c₂,lt_min hc₁ hc₂,?_⟩
  intro n _
  by_cases hn : 13 ≤ n
  · exact (min_le_left _ _).trans (hlarge n hn)
  · exact (min_le_right _ _).trans (hsmall n (by omega))

/-- Every real aspect and every positive scale are covered, conditional only
on the explicit rounded local estimate at integer aspects. -/
theorem selfDual_stripRSW_real_aspect_all_scales_of_rounded_local_connections_from_thirteen
    (q : Set.Ici (1:ℝ))
    (hlocal : ∀ K : ℕ, 1 ≤ K → ∀ n : ℕ, 13 ≤ n →
      selfDualStripHorizontalProbability q K n < 1/2 →
      ∀ j : Fin (18*K), stripLocalLower q K ≤
        (selfDualStripMeasure q n).real
          (stripLocalConnection n ((n+8)/9)
            (stripConnectionShift K ((n+8)/9) j)))
    (k : ℝ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualStripHorizontalProbability q k n :=
  selfDual_stripRSW_real_aspect_of_integer_aspects q (fun n => n)
    (fun K hK => selfDual_stripRSW_all_scales_of_rounded_local_connections_from_thirteen
      q K hK (hlocal K hK)) k hk

end PottsContinuity.RSW
