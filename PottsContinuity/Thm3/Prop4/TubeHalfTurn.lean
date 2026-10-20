module

public import PottsContinuity.Thm3.Prop4.RadiusTube

/-!
# Genuine half-turn geometry for the two excursion cases

Negate the original square and exchange the two endpoints. This preserves
the square even when midpoint recentering would produce a half-integer shift.
The upper and lower tube regions are exchanged exactly.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

@[simp] theorem tubeLatticePoint_neg (z : ℤ × ℤ) :
    tubeLatticePoint (-z) = -tubeLatticePoint z := by
  apply Complex.ext <;> simp [tubeLatticePoint]

theorem tubeDistance_neg (u v z : ℤ × ℤ) :
    tubeDistance (-u) (-v) (-z) = tubeDistance u v z := by
  have hseg : (fun x : ℂ => -x) '' segment ℝ (tubeLatticePoint u) (tubeLatticePoint v) =
      segment ℝ (-tubeLatticePoint u) (-tubeLatticePoint v) := by
    simpa using image_segment ℝ ((-LinearMap.id : ℂ →ₗ[ℝ] ℂ).toAffineMap)
      (tubeLatticePoint u) (tubeLatticePoint v)
  unfold tubeDistance
  rw [tubeLatticePoint_neg,tubeLatticePoint_neg,tubeLatticePoint_neg,← hseg]
  apply Metric.infDist_image
  intro a b
  simp

theorem tubeDistance_neg_swap (u v z : ℤ × ℤ) :
    tubeDistance (-v) (-u) (-z) = tubeDistance u v z := by
  rw [tubeDistance_neg]
  unfold tubeDistance
  rw [segment_symm ℝ (tubeLatticePoint v) (tubeLatticePoint u)]

theorem mem_box_neg_iff (n : ℕ) (z : ℤ × ℤ) : -z ∈ box n ↔ z ∈ box n := by
  simp only [box,Finset.mem_product,Finset.mem_Icc,Prod.fst_neg,Prod.snd_neg]
  omega

theorem radiusTube_neg_swap_mem_iff (n : ℕ) (r : ℝ) (u v z : ℤ × ℤ) :
    -z ∈ radiusTube n r (-v) (-u) ↔ z ∈ radiusTube n r u v := by
  rw [mem_radiusTube,mem_radiusTube,mem_box_neg_iff,tubeDistance_neg_swap]

theorem tubeLineOffset_neg_swap (u v z : ℤ × ℤ) :
    tubeLineOffset (-v) (-u) (-z) = -tubeLineOffset u v z := by
  simp only [tubeLineOffset,Prod.fst_neg,Prod.snd_neg]
  ring

/-- The actual source upper region becomes the lower region after rotating the original box. -/
theorem inductionTubeAbove_neg_swap_mem_iff (n : ℕ) (ε : ℝ) (u v z : ℤ × ℤ) :
    -z ∈ inductionTubeAbove n ε (-v) (-u) ↔ z ∈ inductionTubeBelow n ε u v := by
  classical
  have hTube : -z ∈ inductionTube n ε (-v) (-u) ↔ z ∈ inductionTube n ε u v := by
    rw [inductionTube_eq_radiusTube,inductionTube_eq_radiusTube,radiusTube_neg_swap_mem_iff]
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    refine Finset.mem_filter.mpr ⟨(mem_box_neg_iff n z).mp hh.1,
      (not_congr hTube).mp hh.2.1,?_⟩
    have ho := hh.2.2
    rw [tubeLineOffset_neg_swap] at ho
    exact neg_pos.mp ho
  · intro h
    have hh := Finset.mem_filter.mp h
    refine Finset.mem_filter.mpr ⟨(mem_box_neg_iff n z).mpr hh.1,
      (not_congr hTube).mpr hh.2.1,?_⟩
    rw [tubeLineOffset_neg_swap]
    exact neg_pos.mpr hh.2.2

/-- The half-turn preserves the exact opposite-face endpoint hypotheses after exchanging endpoints. -/
theorem tube_opposite_faces_neg_swap (n : ℕ) (u v : ℤ × ℤ)
    (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ)) :
    (-v).1 = -(n : ℤ) ∧ (-u).1 = (n : ℤ) := by
  simp [hu,hv]

end PottsContinuity.Thm3.Prop4
