module

public import PottsContinuity.Thm3.Prop4.DenominatorDescent
public import PottsContinuity.Thm3.Prop4.TouchUnion

/-!
# Touch averaging with a denominator at most twice the horizontal radius

The actual source descent has radius n*d*m. For d≤2m its candidate count
still gives the absolute polynomial factor 20, uniformly in all scales.
The duality-half bound and the explored-strip comparison are hypotheses of the
probability lemmas here. For the self-dual strip law the comparison is
`selfDual_tilted_isolation_probability_le_touch` (used in `Thm3.Prop4.TouchHalfConsumer`),
and the half-height bound follows from
`PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half` with the reduced marginal
identity `RSW.selfDual_tiltedStrip_reflected_marginal`.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Actual corrected candidate count for a bounded independent denominator. -/
theorem denominatorCandidates_twice_card_le (n m d : ℕ) (t : ℝ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hdm : d ≤ 2*m) :
    2*((tiltedCandidates n (n*d*m) t).card : ℝ) ≤ 20*(n : ℝ)^2*(m : ℝ)^2 := by
  have hR : n*d*m ≤ 2*n*m^2 := by
    calc
      n*d*m = (n*m)*d := by ring
      _ ≤ (n*m)*(2*m) := Nat.mul_le_mul_left _ hdm
      _ = 2*n*m^2 := by ring
  have hcard := (tiltedCandidates_card_le n (n*d*m) t).trans
    (Nat.mul_le_mul_right (n+1) (show 2*(n*d*m)+1 ≤ 4*n*m^2+1 by
      calc
        _ ≤ 2*(2*n*m^2)+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hR) 1
        _ = _ := by ring))
  have hcardR : ((tiltedCandidates n (n*d*m) t).card : ℝ) ≤
      (4*(n : ℝ)*(m : ℝ)^2+1)*((n : ℝ)+1) := by exact_mod_cast hcard
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (1 : ℝ) ≤ (n : ℝ)*(m : ℝ)^2 :=
    (one_le_pow₀ hmR).trans (le_mul_of_one_le_left (sq_nonneg _) hnR)
  calc
    _ ≤ 2*((4*(n : ℝ)*(m : ℝ)^2+1)*((n : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hcardR (by norm_num)
    _ ≤ 2*((5*(n : ℝ)*(m : ℝ)^2)*(2*(n : ℝ))) := by
      gcongr <;> linarith only [hnR,hnm]
    _ = 20*(n : ℝ)^2*(m : ℝ)^2 := by ring

/-- The actual low-height event is covered by A(x) within radius n*d*m. -/
theorem low_height_subset_denominatorIsolation_union (n m d : ℕ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (htd : ∃ a : ℤ, t*(d : ℝ) = a) :
    {ω : TiltedConfiguration (2*n) t |
      lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} ⊆
      ⋃ z ∈ tiltedCandidates n (n*d*m) t, tiltedIsolationAt (2*n) n m t z := by
  intro ω hω
  obtain ⟨k, hk, hFk, hmin⟩ :=
    lowestTopConnectedHeight_local_minimum_denominator n m d hn hd t htd ω hω
  obtain ⟨hx,hA⟩ := local_minimum_implies_touchIsolation n m hn t ht ω k hFk hmin
  have hz : (k,lowestTopConnectedVertex (2*n) (by omega) t ω k) ∈
      tiltedCandidates n (n*d*m) t := by
    apply (mem_tiltedCandidates _ _ _ _).mpr
    refine ⟨?_, (lowestTopConnectedHeight_mem (2*n) (by omega) t ω k).1, hFk⟩
    simpa only [Nat.cast_mul] using hk
  exact Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨hz,hx,hA⟩⟩

/-- Bounded-denominator version of the corrected A(x) probability estimate. -/
theorem exists_denominatorIsolation_lower_of_dualityHalf
    (n m d : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hd : 1 ≤ d) (hdm : d ≤ 2*m)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (htd : ∃ a : ℤ, t*(d : ℝ) = a)
    (μ : Measure (TiltedConfiguration (2*n) t)) [IsProbabilityMeasure μ]
    (hhalf : (1/2 : ℝ) ≤ μ.real
      {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n}) :
    ∃ z ∈ tiltedCandidates n (n*d*m) t,
      1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤ μ.real (tiltedIsolationAt (2*n) n m t z) := by
  classical
  let S := tiltedCandidates n (n*d*m) t
  let p : ℤ × ℤ → ℝ := fun z => μ.real (tiltedIsolationAt (2*n) n m t z)
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image S p (tiltedCandidates_nonempty _ _ _)
  have hsum : (1/2 : ℝ) ≤ ∑ y ∈ S, p y := by
    exact hhalf.trans ((measureReal_mono
      (low_height_subset_denominatorIsolation_union n m d hn hd t ht htd)
      (measure_ne_top μ _)).trans (measureReal_biUnion_finset_le _ _))
  have havg : (1/2 : ℝ) ≤ (S.card : ℝ)*p z := by
    calc
      _ ≤ ∑ y ∈ S, p y := hsum
      _ ≤ ∑ y ∈ S, p z := Finset.sum_le_sum (fun y hy => hmax y hy)
      _ = _ := by simp
  have hprod := mul_le_mul_of_nonneg_right (denominatorCandidates_twice_card_le n m d t hn hm hdm)
    (show 0 ≤ p z from measureReal_nonneg)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨z,hz,(div_le_iff₀ (by positivity : 0 < 20*(n : ℝ)^2*(m : ℝ)^2)).mpr ?_⟩
  change 1 ≤ p z*(20*(n : ℝ)^2*(m : ℝ)^2)
  change 2*(S.card : ℝ)*p z ≤ (20*(n : ℝ)^2*(m : ℝ)^2)*p z at hprod
  nlinarith only [havg,hprod]

/-- Exact finite touch estimate from bounded-denominator duality-half and
exploration comparison. Both probability inputs are explicit hypotheses. -/
theorem tilted_touch_denominator_corrected_of_dualityHalf_and_stripComparison
    (θ : PD.FK.Parameters) (n m d : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hd : 1 ≤ d) (hdm : d ≤ 2*m) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (htd : ∃ a : ℤ, t*(d : ℝ) = a)
    (μ : Measure (TiltedConfiguration (2*n) t)) [IsProbabilityMeasure μ]
    (hhalf : (1/2 : ℝ) ≤ μ.real
      {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n})
    (hcomparison : ∀ z ∈ tiltedCandidates n (n*d*m) t,
      μ.real (tiltedIsolationAt (2*n) n m t z) ≤ tiltedTouchProbability θ n m t) :
    1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤ tiltedTouchProbability θ n m t := by
  obtain ⟨z,hz,hA⟩ := exists_denominatorIsolation_lower_of_dualityHalf
    n m d hn hm hd hdm t ht htd μ hhalf
  exact hA.trans (hcomparison z hz)

end PottsContinuity.Thm3.Prop4
