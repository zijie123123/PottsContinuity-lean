module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

/-!
# A bounded-denominator slope in the same finite lattice-comparison cell

For a box of radius m, supporting-line comparisons can only change at
rational slopes a/d with 1≤d≤m. Between consecutive such breakpoints a
mediant has denominator at most 2m. At a breakpoint its own denominator is
already at most m. This is a deterministic construction, independent of FK.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every possible supporting-line breakpoint with nonzero column |x|≤m,
restricted to the source slope interval [-1,1]. -/
noncomputable def slopeBreakpoints (m : ℕ) : Finset ℝ := by
  classical
  exact (Finset.Icc 1 m).biUnion (fun d =>
    (Finset.Icc (-(d : ℤ)) (d : ℤ)).image (fun a : ℤ => (a : ℝ)/(d : ℝ)))

/-- A breakpoint has its displayed positive denominator bounded by m. -/
theorem mem_slopeBreakpoints (m : ℕ) (b : ℝ) : b ∈ slopeBreakpoints m ↔
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ m ∧ ∃ a : ℤ, -(d : ℤ) ≤ a ∧ a ≤ d ∧ b = (a : ℝ)/d := by
  classical
  simp only [slopeBreakpoints, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨d, ⟨hd, hdm⟩, a, ⟨ha, had⟩, hb⟩
    exact ⟨d, hd, hdm, a, ha, had, hb.symm⟩
  · rintro ⟨d, hd, hdm, a, ha, had, rfl⟩
    exact ⟨d, ⟨hd, hdm⟩, a, ⟨ha, had⟩, rfl⟩

/-- All finite breakpoints are in the source slope interval. -/
theorem slopeBreakpoints_bounds (m : ℕ) {b : ℝ} (hb : b ∈ slopeBreakpoints m) :
    b ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨d, hd, _, a, ha, had, rfl⟩ := (mem_slopeBreakpoints m b).mp hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdR).mpr
    have h : -(d : ℝ) ≤ a := by exact_mod_cast ha
    linarith only [h]
  · apply (div_le_iff₀ hdR).mpr
    have h : (a : ℝ) ≤ d := by exact_mod_cast had
    simpa only [one_mul] using h

/-- Both endpoints are included whenever m≥1. -/
theorem slopeBreakpoints_endpoints (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℝ) ∈ slopeBreakpoints m ∧ (1 : ℝ) ∈ slopeBreakpoints m := by
  constructor
  · exact (mem_slopeBreakpoints m (-1)).mpr ⟨1, le_rfl, hm, -1, by norm_num, by norm_num, by norm_num⟩
  · exact (mem_slopeBreakpoints m 1).mpr ⟨1, le_rfl, hm, 1, by norm_num, by norm_num, by norm_num⟩

/-- A mediant lies strictly between two ordered fractions of positive denominators. -/
theorem mediant_strict_between {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a/b < c/d) : a/b < (a+c)/(b+d) ∧ (a+c)/(b+d) < c/d := by
  have hcross := (div_lt_div_iff₀ hb hd).mp h
  constructor
  · apply (div_lt_div_iff₀ hb (add_pos hb hd)).mpr
    nlinarith only [hcross]
  · apply (div_lt_div_iff₀ (add_pos hb hd) hd).mpr
    nlinarith only [hcross]

/-- Every source slope has a rational representative of denominator ≤2m
with exactly the same strict and non-strict comparisons against all breakpoints. -/
theorem exists_bounded_denominator_same_cell (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ (d : ℕ) (a : ℤ), 1 ≤ d ∧ d ≤ 2*m ∧
      (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∀ b ∈ slopeBreakpoints m,
        (t < b ↔ (a : ℝ)/(d : ℝ) < b) ∧ (t ≤ b ↔ (a : ℝ)/(d : ℝ) ≤ b) := by
  classical
  by_cases htB : t ∈ slopeBreakpoints m
  · obtain ⟨d, hd, hdm, a, _, _, heq⟩ := (mem_slopeBreakpoints m t).mp htB
    exact ⟨d, a, hd, by omega, heq ▸ ht, by intro b _; rw [heq]; exact ⟨Iff.rfl,Iff.rfl⟩⟩
  · have hend := slopeBreakpoints_endpoints m hm
    have htlo : (-1 : ℝ) < t := lt_of_le_of_ne ht.1 (by
      intro heq; exact htB (heq ▸ hend.1))
    have hthi : t < 1 := lt_of_le_of_ne ht.2 (by
      intro heq; exact htB (heq.symm ▸ hend.2))
    let L := (slopeBreakpoints m).filter (fun b => b < t)
    let U := (slopeBreakpoints m).filter (fun b => t < b)
    have hL : L.Nonempty := ⟨-1, Finset.mem_filter.mpr ⟨hend.1, htlo⟩⟩
    have hU : U.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨hend.2, hthi⟩⟩
    obtain ⟨lo, hlo, hloMax⟩ := Finset.exists_max_image L (fun x => x) hL
    obtain ⟨hi, hhi, hhiMin⟩ := Finset.exists_min_image U (fun x => x) hU
    obtain ⟨hloB, hlot⟩ := Finset.mem_filter.mp hlo
    obtain ⟨hhiB, hthi'⟩ := Finset.mem_filter.mp hhi
    obtain ⟨b, hb, hbm, a, _, _, heqlo⟩ := (mem_slopeBreakpoints m lo).mp hloB
    obtain ⟨d, hd, hdm, c, _, _, heqhi⟩ := (mem_slopeBreakpoints m hi).mp hhiB
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hmid := mediant_strict_between hbR hdR
      (show (a : ℝ)/(b : ℝ) < (c : ℝ)/(d : ℝ) by rw [← heqlo, ← heqhi]; exact hlot.trans hthi')
    let s : ℝ := ((a+c : ℤ) : ℝ)/((b+d : ℕ) : ℝ)
    have hlos : lo < s := by simpa only [s, Int.cast_add, Nat.cast_add, heqlo] using hmid.1
    have hshi : s < hi := by simpa only [s, Int.cast_add, Nat.cast_add, heqhi] using hmid.2
    refine ⟨b+d, a+c, by omega, by omega, ?_, ?_⟩
    · exact ⟨(slopeBreakpoints_bounds m hloB).1.trans hlos.le,
        hshi.le.trans (slopeBreakpoints_bounds m hhiB).2⟩
    · intro z hz
      have hzt : z ≠ t := by intro h; exact htB (h ▸ hz)
      rcases lt_or_gt_of_ne hzt with hzt | htz
      · have hzlo : z ≤ lo := hloMax z (Finset.mem_filter.mpr ⟨hz,hzt⟩)
        have hzs : z < s := hzlo.trans_lt hlos
        constructor <;> constructor <;> intro h <;> linarith only [hzt,hzs,h]
      · have hhiz : hi ≤ z := hhiMin z (Finset.mem_filter.mpr ⟨hz,htz⟩)
        have hsz : s < z := hshi.trans_le hhiz
        constructor <;> constructor <;> intro h <;> linarith only [htz,hsz,h]

end PottsContinuity.Thm3.Prop4
