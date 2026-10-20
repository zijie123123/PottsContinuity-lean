module

public import PottsContinuity.Thm3.Prop4.FiniteSlope
public import PottsContinuity.Thm3.Prop4.TiltedGeometry

/-!
# Exact finite lattice geometry within a slope cell

The same-cell representative preserves every supporting-line comparison in
columns |x|≤m, including equality at lattice boundary vertices. Consequently
it preserves the actual finite vertex set and the digital top designation.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

private theorem same_cell_positive_column (m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b))
    (x y : ℤ) (hx : 0 < x) (hxm : x ≤ (m : ℤ)) :
    (t*(x : ℝ) < y ↔ s*(x : ℝ) < y) ∧
      (t*(x : ℝ) ≤ y ↔ s*(x : ℝ) ≤ y) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  by_cases hlo : y < -x
  · have hloR : (y : ℝ) < -(x : ℝ) := by exact_mod_cast hlo
    have htlo := mul_le_mul_of_nonneg_right ht.1 hxR.le
    have hslo := mul_le_mul_of_nonneg_right hs.1 hxR.le
    simp only [neg_one_mul] at htlo hslo
    constructor <;> constructor <;> intro h <;> linarith only [hloR,htlo,hslo,h]
  · by_cases hhi : x < y
    · have hhiR : (x : ℝ) < y := by exact_mod_cast hhi
      have hthi := mul_le_mul_of_nonneg_right ht.2 hxR.le
      have hshi := mul_le_mul_of_nonneg_right hs.2 hxR.le
      simp only [one_mul] at hthi hshi
      constructor <;> constructor <;> intro h <;> linarith only [hhiR,hthi,hshi]
    · have hdcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx.le
      have hdR : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast hdcast
      have hd : 1 ≤ x.toNat := by omega
      have hdm : x.toNat ≤ m := by omega
      have hb : (y : ℝ)/(x : ℝ) ∈ slopeBreakpoints m := by
        apply (mem_slopeBreakpoints m _).mpr
        exact ⟨x.toNat, hd, hdm, y, by omega, by omega, by rw [hdR]⟩
      simpa only [lt_div_iff₀ hxR, le_div_iff₀ hxR] using hcell _ hb

/-- Both strict and non-strict supporting-line comparisons are preserved in
every column of the actual finite box, for every integer row threshold. -/
theorem same_cell_column_comparisons (m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b))
    (x y : ℤ) (hxm : |x| ≤ (m : ℤ)) :
    (t*(x : ℝ) < y ↔ s*(x : ℝ) < y) ∧
      (t*(x : ℝ) ≤ y ↔ s*(x : ℝ) ≤ y) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos := same_cell_positive_column m t s ht hs hcell (-x) (-y) (by omega)
      (by have := abs_le.mp hxm; omega)
    simp only [Int.cast_neg, mul_neg, neg_lt_neg_iff, neg_le_neg_iff] at hpos
    exact ⟨by simpa only [not_le] using not_congr hpos.2,
      by simpa only [not_lt] using not_congr hpos.1⟩
  · simp
  · exact same_cell_positive_column m t s ht hs hcell x y hx ((abs_le.mp hxm).2)

/-- Exact agreement of strip membership in the bounded columns, with all
lattice boundary equalities retained. -/
theorem same_cell_strip_membership (n m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b))
    (z : ℤ × ℤ) (hz : |z.1| ≤ (m : ℤ)) :
    z ∈ tiltedStripVertices n t ↔ z ∈ tiltedStripVertices n s := by
  have hlo := (same_cell_column_comparisons m t s ht hs hcell z.1 z.2 hz).2
  have hhi := (same_cell_column_comparisons m t s ht hs hcell z.1 (z.2-(n : ℤ)) hz).1
  push_cast at hhi
  constructor
  · rintro ⟨hzt,hnt⟩
    have hl := hlo.mp (by dsimp [tiltedHeight] at hzt; linarith only [hzt])
    have hh : ¬s*(z.1 : ℝ) < (z.2 : ℝ)-n := (not_congr hhi).mp (by
      dsimp [tiltedHeight] at hnt
      linarith only [hnt])
    constructor <;> dsimp [tiltedHeight] <;> linarith only [hl,hh]
  · rintro ⟨hzs,hns⟩
    have hl := hlo.mpr (by dsimp [tiltedHeight] at hzs; linarith only [hzs])
    have hh : ¬t*(z.1 : ℝ) < (z.2 : ℝ)-n := (not_congr hhi).mpr (by
      dsimp [tiltedHeight] at hns
      linarith only [hns])
    constructor <;> dsimp [tiltedHeight] <;> linarith only [hl,hh]

/-- Exact equality of the finite induced vertex sets at two slopes in one cell. -/
theorem same_cell_tiltedWindow_eq (n m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b)) :
    tiltedWindow n m t = tiltedWindow n m s := by
  ext z
  rw [mem_tiltedWindow,mem_tiltedWindow]
  by_cases hz : z ∈ box m
  · exact and_congr_right (fun _ => same_cell_strip_membership n m t s ht hs hcell z
      ((Foundations.mem_box_iff_abs_le m z).mp hz).1)
  · simp only [hz, false_and]

/-- The digital top predicate is also exactly preserved in every box column. -/
theorem same_cell_tiltedTop_iff (n m : ℕ) (t s : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hcell : ∀ b ∈ slopeBreakpoints m, (t<b ↔ s<b) ∧ (t≤b ↔ s≤b))
    (z : ℤ × ℤ) (hz : |z.1| ≤ (m : ℤ)) : tiltedTop n t z ↔ tiltedTop n s z := by
  rw [tiltedTop_iff_height n ht, tiltedTop_iff_height n hs]
  have h := (same_cell_column_comparisons m t s ht hs hcell z.1 (z.2+1-(n : ℤ)) hz).1
  push_cast at h
  constructor
  · intro hzt
    have hh := h.mp (by dsimp [tiltedHeight] at hzt; linarith only [hzt])
    dsimp [tiltedHeight]
    linarith only [hh]
  · intro hzs
    have hh := h.mpr (by dsimp [tiltedHeight] at hzs; linarith only [hzs])
    dsimp [tiltedHeight]
    linarith only [hh]

end PottsContinuity.Thm3.Prop4
