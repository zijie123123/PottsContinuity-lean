module

public import PottsContinuity.Thm3.Prop4.TranslatedWindowIso

/-! # Explicit ambient containment and the finite source comparison bound -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Every integer lattice point belongs to a specified finite frozen box. -/
theorem lattice_point_mem_some_box (x : ℤ × ℤ) : ∃ R : ℕ, x ∈ box R := by
  refine ⟨x.1.natAbs+x.2.natAbs,(Foundations.mem_box_iff_abs_le _ x).mpr ?_⟩
  simp only [Nat.cast_add,Int.natCast_natAbs]
  have hx := abs_nonneg x.1
  have hy := abs_nonneg x.2
  constructor <;> omega

/-- Translation increases the containing box by at most the target box radius. -/
theorem translatedTiltedWindow_subset_box (n m R : ℕ) (t : ℝ) (x : ℤ × ℤ)
    (hx : x ∈ box R) : translatedTiltedWindow n m t x ⊆ (box (R+m) : Set (ℤ × ℤ)) := by
  intro z hz
  have hrel := ((mem_tiltedWindow n m t (z-x)).mp hz).1
  have hxI := (Foundations.mem_box_iff_interval R x).mp hx
  have hzI := (Foundations.mem_box_iff_interval m (z-x)).mp hrel
  apply (Foundations.mem_box_iff_interval (R+m) z).mpr
  dsimp at hzI
  push_cast
  omega

/-- Height bounds alone place the whole translated target in the ambient infinite strip. -/
theorem translatedTiltedWindow_subset_strip_of_height (N n m : ℕ) (t : ℝ)
    (x : ℤ × ℤ) (hx0 : 0 ≤ tiltedHeight t x)
    (hxN : tiltedHeight t x+(n : ℝ) ≤ N) :
    translatedTiltedWindow n m t x ⊆ tiltedStripVertices N t := by
  intro z hz
  have hrel := ((mem_tiltedWindow n m t (z-x)).mp hz).2
  change 0 ≤ tiltedHeight t (z-x) ∧ tiltedHeight t (z-x) ≤ n at hrel
  rw [tiltedHeight_sub] at hrel
  constructor <;> linarith only [hrel.1,hrel.2,hx0,hxN]

/-- The entire translated target is retained from an explicit ambient truncation onward. -/
theorem translatedTiltedWindow_subset_window (N n m R M : ℕ) (t : ℝ) (x : ℤ × ℤ)
    (hx : x ∈ box R) (hx0 : 0 ≤ tiltedHeight t x)
    (hxN : tiltedHeight t x+(n : ℝ) ≤ N) (hM : R+m ≤ M) :
    translatedTiltedWindow n m t x ⊆ (tiltedWindow N M t : Set (ℤ × ℤ)) := by
  intro z hz
  apply (mem_tiltedWindow N M t z).mpr
  refine ⟨?_,translatedTiltedWindow_subset_strip_of_height N n m t x hx0 hxN hz⟩
  have hbox := translatedTiltedWindow_subset_box n m R t x hx hz
  have hzI := (Foundations.mem_box_iff_interval (R+m) z).mp hbox
  have hcast : (R : ℤ)+(m : ℤ) ≤ M := by exact_mod_cast hM
  apply (Foundations.mem_box_iff_interval M z).mpr
  push_cast at hzI
  omega

/-- Finite part of eq. (23), with the original touch probability and no remaining law interface. -/
theorem tilted_finite_isolation_le_touch (θ : Parameters) (N M n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (x : (tiltedWindow N M t : Set (ℤ × ℤ)))
    (hxheight : tiltedHeight t x.val+(n : ℝ) ≤ N)
    (hcontain : translatedTiltedWindow n m t x.val ⊆ (tiltedWindow N M t : Set (ℤ × ℤ))) :
    (measure (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) θ
      (tiltedWindowBoundary N M t 0)
      (finiteArcIsolationEvent (translatedWindowDomain N M n m t x.val)
        (translatedWindowArc N M n m t x.val) x)).toReal ≤ tiltedTouchProbability θ n m t := by
  have h := translatedWindow_finite_isolation_probability_le θ N M n m t ht x hxheight
  have heq := translatedWindow_target_probability_eq θ N M n m t x.val hcontain
  have hroot : translatedTiltedWindowIso N M n m t x.val hcontain (tiltedWindowOrigin n m t) =
      ⟨x,mem_translatedTiltedWindow_self n m t x.val⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_zero x.val
  dsimp only at heq
  rw [hroot] at heq
  exact h.trans heq.le

end
end PottsContinuity.Thm3.Prop4
