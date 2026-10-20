module

public import PottsContinuity.Thm3.Prop4.TailRecursion
public import PottsContinuity.Thm3.Prop4.Decay
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# The genuine tail supremum in Proposition 4

DCST, TeX lines 1791–1821. The supremum is defined for a sequence proved to
converge to zero, so it is bounded on its whole stated carrier. Nonnegative
sequences attain every tail supremum, including the identically zero case.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Actual tail supremum of a sequence with a proved zero limit. -/
noncomputable def convergentTailSup (u : ℕ → ℝ) (_hlim : Tendsto u atTop (𝓝 0))
    (n : ℕ) : ℝ := sSup (u '' Set.Ici n)

/-- A tail value is below the actual tail supremum. -/
theorem le_convergentTailSup (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0))
    {n m : ℕ} (hnm : n ≤ m) : u m ≤ convergentTailSup u hlim n := by
  apply le_csSup
  · exact hlim.bddAbove_range.mono (by rintro _ ⟨i, _, rfl⟩; exact Set.mem_range_self i)
  · exact ⟨m, hnm, rfl⟩

/-- A uniform tail upper bound bounds its supremum. -/
theorem convergentTailSup_le (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0))
    (n : ℕ) (b : ℝ) (hb : ∀ m, n ≤ m → u m ≤ b) :
    convergentTailSup u hlim n ≤ b := by
  apply csSup_le
  · exact ⟨u n, n, Set.mem_Ici.mpr (le_refl n), rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hb m hm

/-- Tail suprema decrease with the starting index. -/
theorem convergentTailSup_antitone (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0)) :
    Antitone (convergentTailSup u hlim) := by
  intro n m hnm
  exact convergentTailSup_le u hlim m _ (fun k hmk =>
    le_convergentTailSup u hlim (hnm.trans hmk))

/-- A nonnegative convergent sequence attains its maximum on every tail. -/
theorem exists_tail_maximum (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0))
    (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ ∀ k, n ≤ k → u k ≤ u m := by
  classical
  by_cases hpos : ∃ i : ℕ, n ≤ i ∧ 0 < u i
  · obtain ⟨i, hni, hi⟩ := hpos
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hi))
    let s := Finset.Icc n (max N i)
    have hne : s.Nonempty := ⟨i, Finset.mem_Icc.mpr ⟨hni, le_max_right _ _⟩⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s u hne
    refine ⟨m, (Finset.mem_Icc.mp hm).1, ?_⟩
    intro k hnk
    by_cases hk : k ≤ max N i
    · exact hmax k (Finset.mem_Icc.mpr ⟨hnk, hk⟩)
    · exact (hN k (by omega)).le.trans (hmax i (Finset.mem_Icc.mpr ⟨hni, le_max_right _ _⟩))
  · refine ⟨n, le_rfl, ?_⟩
    intro k hnk
    have hk : u k ≤ 0 := by
      by_contra h
      exact hpos ⟨k, hnk, lt_of_not_ge h⟩
    exact hk.trans (hu n)

/-- The supremum equals an actual tail value; no arbitrary near-maximizer is selected. -/
theorem convergentTailSup_attained (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0))
    (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ convergentTailSup u hlim n = u m := by
  obtain ⟨m, hnm, hm⟩ := exists_tail_maximum u hlim hu n
  exact ⟨m, hnm, le_antisymm (convergentTailSup_le u hlim n _ hm)
    (le_convergentTailSup u hlim hnm)⟩

/-- The decreasing nonnegative tail envelope also tends to zero. -/
theorem convergentTailSup_tendsto_zero (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0))
    (hu : ∀ n, 0 ≤ u n) : Tendsto (convergentTailSup u hlim) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      ((hu n).trans (le_convergentTailSup u hlim le_rfl)))
  · intro b hb
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hb)))
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (convergentTailSup_le u hlim n (b/2)
      (fun k hk => (hN k (hn.trans hk)).le)).trans_lt (by linarith only [hb])

/-- Passing an attained product recursion to Q_n=C*sup_{m≥n}u_m. This is the
numeric envelope step with an explicit monotone cutoff, not an FK graph export. -/
theorem envelope_product_recursion_of_attainedRecursion
    (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0)) (hu : ∀ n, 0 ≤ u n)
    (C : ℝ) (hC : 0 < C) (r : ℕ → ℕ) (hr : Monotone r)
    (hrec : ∀ n, 1 ≤ n →
      ∃ k l : ℕ, r n ≤ k ∧ r n ≤ l ∧ n ≤ k+l ∧ u n ≤ C*u k*u l)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k l : ℕ, r n ≤ k ∧ r n ≤ l ∧ n ≤ k+l ∧
      C*convergentTailSup u hlim n ≤
        (C*convergentTailSup u hlim k)*(C*convergentTailSup u hlim l) := by
  obtain ⟨m, hnm, hm⟩ := convergentTailSup_attained u hlim hu n
  obtain ⟨k, l, hk, hl, hsum, hprod⟩ := hrec m (hn.trans hnm)
  refine ⟨k, l, (hr hnm).trans hk, (hr hnm).trans hl, hnm.trans hsum, ?_⟩
  rw [hm]
  have hkQ := le_convergentTailSup u hlim (n := k) le_rfl
  have hlQ := le_convergentTailSup u hlim (n := l) le_rfl
  have hprodQ : u k*u l ≤ convergentTailSup u hlim k*convergentTailSup u hlim l :=
    mul_le_mul hkQ hlQ (hu l) ((hu k).trans hkQ)
  calc
    C*u m ≤ C*(C*u k*u l) := mul_le_mul_of_nonneg_left hprod hC.le
    _ = (C*C)*(u k*u l) := by ring
    _ ≤ (C*C)*(convergentTailSup u hlim k*convergentTailSup u hlim l) :=
      mul_le_mul_of_nonneg_left hprodQ (mul_nonneg hC.le hC.le)
    _ = _ := by ring

/-- Complete numeric decay implication from the attained recursion. The actual
supremum, attainment, envelope monotonicity, convergence, truncation, induction,
and prefactor absorption are all proved here, not assumed as extra inputs. -/
theorem exponential_tail_of_attainedRecursion
    (u : ℕ → ℝ) (hlim : Tendsto u atTop (𝓝 0)) (hu : ∀ n, 0 ≤ u n)
    (C : ℝ) (hC : 0 < C) (r : ℕ → ℕ) (hr : Monotone r)
    (hrlim : Tendsto r atTop atTop) (hrlt : ∀ᶠ n in atTop, r n < n)
    (hrec : ∀ n, 1 ≤ n →
      ∃ k l : ℕ, r n ≤ k ∧ r n ≤ l ∧ n ≤ k+l ∧ u n ≤ C*u k*u l) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, u n ≤ Real.exp (-c*(n : ℝ)) := by
  let Q : ℕ → ℝ := fun n => C*convergentTailSup u hlim n
  have huSup (n : ℕ) : 0 ≤ convergentTailSup u hlim n :=
    (hu n).trans (le_convergentTailSup u hlim le_rfl)
  have hQ : ∀ n, 0 ≤ Q n := fun n => mul_nonneg hC.le (huSup n)
  have hanti : Antitone Q := fun n m hnm =>
    mul_le_mul_of_nonneg_left (convergentTailSup_antitone u hlim hnm) hC.le
  have hQlim : Tendsto Q atTop (𝓝 0) := by
    simpa only [mul_zero] using (convergentTailSup_tendsto_zero u hlim hu).const_mul C
  have hQrec : ∀ n, 1 ≤ n →
      ∃ k l : ℕ, r n ≤ k ∧ r n ≤ l ∧ n ≤ k+l ∧ Q n ≤ Q k*Q l :=
    envelope_product_recursion_of_attainedRecursion u hlim hu C hC r hr hrec
  obtain ⟨c, hc, hbound⟩ :=
    exponential_tail_of_product_recursion Q r hQ hanti hQlim hrlim hrlt hQrec
  have habsorb := eventually_absorb_exponential_prefactor (one_div_pos.mpr hC) hc
  refine ⟨c/2, half_pos hc, ?_⟩
  filter_upwards [hbound, habsorb] with n hn hA
  have huQ : u n*C ≤ Q n := by
    simpa only [Q, mul_comm] using
      mul_le_mul_of_nonneg_left (le_convergentTailSup u hlim (n := n) le_rfl) hC.le
  calc
    u n ≤ Real.exp (-c*(n : ℝ))/C := (le_div_iff₀ hC).mpr (huQ.trans hn)
    _ = (1/C)*Real.exp (-c*(n : ℝ)) := by ring
    _ ≤ Real.exp (-(c/2)*(n : ℝ)) := hA

end PottsContinuity.Thm3.Prop4
