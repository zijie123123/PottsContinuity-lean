module

public import PottsContinuity.Foundations.Bridges

@[expose] public section

namespace PottsContinuity.Foundations

open PottsContinuity

theorem mem_box_iff_interval (n : ℕ) (x : ℤ × ℤ) :
    x ∈ box n ↔
      (-(n : ℤ) ≤ x.1 ∧ x.1 ≤ n) ∧ (-(n : ℤ) ≤ x.2 ∧ x.2 ≤ n) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]

theorem mem_box_iff_abs_le (n : ℕ) (x : ℤ × ℤ) :
    x ∈ box n ↔ |x.1| ≤ n ∧ |x.2| ≤ n := by
  rw [mem_box_iff_interval]
  simp only [abs_le]

private theorem adj_iff (x y : ℤ × ℤ) :
    squareLattice.Adj x y ↔
      y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
        y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) := by
  change |x.1 - y.1| + |x.2 - y.2| = 1 ↔ _
  simp only [abs_eq_max_neg, Prod.ext_iff]
  omega

private theorem abs_eq_natCast_iff (n : ℕ) (z : ℤ) (h : |z| = n) :
    z = n ∨ z = -(n : ℤ) := by
  rcases le_total 0 z with hz | hz
  · left
    simpa [abs_of_nonneg hz] using h
  · right
    have h' : -z = n := by simpa [abs_of_nonpos hz] using h
    omega

private theorem max_abs_eq_side (n : ℕ) (x : ℤ × ℤ)
    (h : max |x.1| |x.2| = n) :
    x.1 = n ∨ x.1 = -(n : ℤ) ∨ x.2 = n ∨ x.2 = -(n : ℤ) := by
  by_cases hxy : |x.1| ≤ |x.2|
  · rw [max_eq_right hxy] at h
    rcases abs_eq_natCast_iff n x.2 h with h2 | h2
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h2))
  · have hyx : |x.2| ≤ |x.1| := le_of_not_ge hxy
    rw [max_eq_left hyx] at h
    rcases abs_eq_natCast_iff n x.1 h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

private theorem exists_adj_outside_box (n : ℕ) (x : ℤ × ℤ)
    (hside : x.1 = n ∨ x.1 = -(n : ℤ) ∨ x.2 = n ∨ x.2 = -(n : ℤ)) :
    ∃ y, squareLattice.Adj x y ∧ y ∉ box n := by
  rcases hside with h | h | h | h
  · refine ⟨(x.1 + 1, x.2), (adj_iff x _).2 (Or.inl rfl), ?_⟩
    intro hy
    have hy' := (mem_box_iff_interval n (x.1 + 1, x.2)).mp hy
    omega
  · refine ⟨(x.1 - 1, x.2), (adj_iff x _).2 (Or.inr (Or.inl rfl)), ?_⟩
    intro hy
    have hy' := (mem_box_iff_interval n (x.1 - 1, x.2)).mp hy
    omega
  · refine ⟨(x.1, x.2 + 1), (adj_iff x _).2 (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
    intro hy
    have hy' := (mem_box_iff_interval n (x.1, x.2 + 1)).mp hy
    omega
  · refine ⟨(x.1, x.2 - 1), (adj_iff x _).2 (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
    intro hy
    have hy' := (mem_box_iff_interval n (x.1, x.2 - 1)).mp hy
    omega

theorem vertexBoundary_box_eq (n : ℕ) :
    vertexBoundary (box n) = {x | max |x.1| |x.2| = (n : ℤ)} := by
  classical
  ext x
  constructor
  · intro hx
    change max |x.1| |x.2| = (n : ℤ)
    rw [vertexBoundary_eq_PD] at hx
    change x ∈ box n ∧ ∃ y, squareLattice.Adj x y ∧ y ∉ box n at hx
    have hxint := (mem_box_iff_interval n x).mp hx.1
    obtain ⟨y, hadj, hyout⟩ := hx.2
    have hyout' : y ∉ box n := hyout
    have hsides : x.1 = n ∨ x.1 = -(n : ℤ) ∨ x.2 = n ∨ x.2 = -(n : ℤ) := by
      rw [adj_iff] at hadj
      rcases hadj with h | h | h | h
      · subst y
        have hy : ¬ ((-(n : ℤ) ≤ x.1 + 1 ∧ x.1 + 1 ≤ n) ∧
            (-(n : ℤ) ≤ x.2 ∧ x.2 ≤ n)) := by
          intro hyint
          apply hyout'
          exact (mem_box_iff_interval n (x.1 + 1, x.2)).mpr hyint
        omega
      · subst y
        have hy : ¬ ((-(n : ℤ) ≤ x.1 - 1 ∧ x.1 - 1 ≤ n) ∧
            (-(n : ℤ) ≤ x.2 ∧ x.2 ≤ n)) := by
          intro hyint
          apply hyout'
          exact (mem_box_iff_interval n (x.1 - 1, x.2)).mpr hyint
        omega
      · subst y
        have hy : ¬ ((-(n : ℤ) ≤ x.1 ∧ x.1 ≤ n) ∧
            (-(n : ℤ) ≤ x.2 + 1 ∧ x.2 + 1 ≤ n)) := by
          intro hyint
          apply hyout'
          exact (mem_box_iff_interval n (x.1, x.2 + 1)).mpr hyint
        omega
      · subst y
        have hy : ¬ ((-(n : ℤ) ≤ x.1 ∧ x.1 ≤ n) ∧
            (-(n : ℤ) ≤ x.2 - 1 ∧ x.2 - 1 ≤ n)) := by
          intro hyint
          apply hyout'
          exact (mem_box_iff_interval n (x.1, x.2 - 1)).mpr hyint
        omega
    rcases hsides with h | h | h | h
    · have h2 : |x.2| ≤ (n : ℤ) := abs_le.mpr hxint.2
      have h1 : |x.1| = (n : ℤ) := by rw [h, abs_of_nonneg (Int.natCast_nonneg n)]
      rw [h1, max_eq_left h2]
    · have h2 : |x.2| ≤ (n : ℤ) := abs_le.mpr hxint.2
      have h1 : |x.1| = (n : ℤ) := by
        have hx1 : x.1 ≤ 0 := by rw [h]; exact neg_nonpos.mpr (Int.natCast_nonneg n)
        rw [abs_of_nonpos hx1, h]
        omega
      rw [h1, max_eq_left h2]
    · have h1 : |x.1| ≤ (n : ℤ) := abs_le.mpr hxint.1
      have h2 : |x.2| = (n : ℤ) := by rw [h, abs_of_nonneg (Int.natCast_nonneg n)]
      rw [h2, max_eq_right h1]
    · have h1 : |x.1| ≤ (n : ℤ) := abs_le.mpr hxint.1
      have h2 : |x.2| = (n : ℤ) := by
        have hx2 : x.2 ≤ 0 := by rw [h]; exact neg_nonpos.mpr (Int.natCast_nonneg n)
        rw [abs_of_nonpos hx2, h]
        omega
      rw [h2, max_eq_right h1]
  · intro hx
    change max |x.1| |x.2| = (n : ℤ) at hx
    have hxint : x ∈ box n := by
      apply (mem_box_iff_abs_le n x).2
      constructor
      · calc
          |x.1| ≤ max |x.1| |x.2| := le_max_left _ _
          _ = n := hx
      · calc
          |x.2| ≤ max |x.1| |x.2| := le_max_right _ _
          _ = n := hx
    have hside := max_abs_eq_side n x hx
    obtain ⟨y, hadj, hyout⟩ := exists_adj_outside_box n x hside
    rw [vertexBoundary_eq_PD]
    exact ⟨hxint, y, hadj, hyout⟩

end PottsContinuity.Foundations
