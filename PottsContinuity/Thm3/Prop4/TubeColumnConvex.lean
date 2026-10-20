module

public import PottsContinuity.Thm3.Prop4.RadiusTube
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Consecutive rows in the literal central tube cut

A Euclidean tube is a thickening of a convex segment. Its intersection with
each vertical column is an interval, and intersecting the two cut columns
retains that property. No rectangular approximation replaces the tube.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Integer points between two points on a column lie on their actual Euclidean segment. -/
theorem tubeLatticePoint_vertical_segment (k a y b : ℤ) (hay : a ≤ y) (hyb : y ≤ b) :
    tubeLatticePoint (k,y) ∈ segment ℝ (tubeLatticePoint (k,a)) (tubeLatticePoint (k,b)) := by
  by_cases hab : a=b
  · have hya : y=a := by omega
    rw [hya]
    exact left_mem_segment ℝ _ _
  have hpos : (0 : ℝ) < (b : ℝ)-(a : ℝ) := by exact_mod_cast (by omega : 0 < b-a)
  have hayR : (a : ℝ) ≤ y := by exact_mod_cast hay
  have hybR : (y : ℝ) ≤ b := by exact_mod_cast hyb
  refine ⟨((b : ℝ)-y)/((b : ℝ)-a),((y : ℝ)-a)/((b : ℝ)-a),
    div_nonneg (sub_nonneg.mpr hybR) hpos.le,
    div_nonneg (sub_nonneg.mpr hayR) hpos.le,?_,?_⟩
  · field_simp
    ring
  · apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,
      Complex.smul_im,tubeLatticePoint,smul_eq_mul] <;> field_simp <;> ring

/-- The exact open Euclidean tube is convex, including the empty nonpositive-radius cases. -/
theorem convex_euclidean_tube (u v : ℤ × ℤ) (r : ℝ) :
    Convex ℝ {z : ℂ | Metric.infDist z
      (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) < r} := by
  have heq : {z : ℂ | Metric.infDist z
      (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) < r} =
      Metric.thickening r (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) := by
    ext z
    exact (Metric.mem_thickening_iff_infDist_lt ⟨tubeLatticePoint u,left_mem_segment ℝ _ _⟩).symm
  rw [heq]
  exact (convex_segment (tubeLatticePoint u) (tubeLatticePoint v)).thickening r

/-- Intermediate integer rows in a column stay inside the literal finite tube. -/
theorem radiusTube_column_interval (n : ℕ) (r : ℝ) (u v : ℤ × ℤ)
    (k a y b : ℤ) (ha : (k,a) ∈ radiusTube n r u v) (hb : (k,b) ∈ radiusTube n r u v)
    (hay : a ≤ y) (hyb : y ≤ b) : (k,y) ∈ radiusTube n r u v := by
  obtain ⟨haBox,haDist⟩ := (mem_radiusTube n r u v (k,a)).mp ha
  obtain ⟨hbBox,hbDist⟩ := (mem_radiusTube n r u v (k,b)).mp hb
  apply (mem_radiusTube n r u v (k,y)).mpr
  constructor
  · simp only [box,Finset.mem_product,Finset.mem_Icc] at haBox hbBox ⊢
    exact ⟨haBox.1,by omega⟩
  · exact (convex_euclidean_tube u v r).segment_subset haDist hbDist
      (tubeLatticePoint_vertical_segment k a y b hay hyb)

/-- No integer row between two cut rows is omitted from the actual cut. -/
theorem radiusTubeCutRows_interval (n : ℕ) (r : ℝ) (u v : ℤ × ℤ)
    (k a y b : ℤ) (ha : a ∈ radiusTubeCutRows n r u v k)
    (hb : b ∈ radiusTubeCutRows n r u v k) (hay : a ≤ y) (hyb : y ≤ b) :
    y ∈ radiusTubeCutRows n r u v k := by
  classical
  obtain ⟨haBox,ha₀,ha₁⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbBox,hb₀,hb₁⟩ := Finset.mem_filter.mp hb
  apply Finset.mem_filter.mpr
  refine ⟨?_,radiusTube_column_interval n r u v k a y b ha₀ hb₀ hay hyb,
    radiusTube_column_interval n r u v (k+1) a y b ha₁ hb₁ hay hyb⟩
  rw [Finset.mem_Icc] at haBox hbBox ⊢
  omega

/-- Every nonempty cut has exact lowest and highest rows, and contains every row between them. -/
theorem radiusTubeCutRows_eq_interval (n : ℕ) (r : ℝ) (u v : ℤ × ℤ) (k : ℤ)
    (hne : (radiusTubeCutRows n r u v k).Nonempty) :
    ∃ a b : ℤ, a ≤ b ∧ radiusTubeCutRows n r u v k = Finset.Icc a b := by
  classical
  let S := radiusTubeCutRows n r u v k
  refine ⟨S.min' hne,S.max' hne,Finset.min'_le S _ (Finset.max'_mem S hne),?_⟩
  ext y
  constructor
  · intro hy
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le S y hy,Finset.le_max' S y hy⟩
  · intro hy
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hy
    exact radiusTubeCutRows_interval n r u v k (S.min' hne) y (S.max' hne)
      (Finset.min'_mem S hne) (Finset.max'_mem S hne) hlo hhi

end PottsContinuity.Thm3.Prop4
