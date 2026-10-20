module

public import PottsContinuity.Thm3.Touch.InfiniteColumnSlopeReflection
public import PottsContinuity.Thm3.Prop4.TiltedBoundaryLimits
public import PottsContinuity.PD.Duality.BoxDihedral

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open Filter MeasureTheory Topology
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4

noncomputable section

 theorem mem_tiltedWindow_horizontalReflection (n m : ℕ) (t : ℝ)
    (z : ℤ × ℤ) :
    (-z.1,z.2) ∈ tiltedWindow n m (-t) ↔ z ∈ tiltedWindow n m t := by
  rw [mem_tiltedWindow, mem_tiltedWindow]
  constructor
  · rintro ⟨hbox,hstrip⟩
    refine ⟨?_, ?_⟩
    · rw [Foundations.mem_box_iff_abs_le] at hbox ⊢
      simpa [abs_neg] using hbox
    · change 0 ≤ tiltedHeight (-t) (-z.1,z.2) ∧
        tiltedHeight (-t) (-z.1,z.2) ≤ (n : ℝ) at hstrip
      rw [tiltedHeight_columnSlopeReflection] at hstrip
      exact hstrip
  · rintro ⟨hbox,hstrip⟩
    refine ⟨?_, ?_⟩
    · rw [Foundations.mem_box_iff_abs_le] at hbox ⊢
      simpa [abs_neg] using hbox
    · change 0 ≤ tiltedHeight (-t) (-z.1,z.2) ∧
        tiltedHeight (-t) (-z.1,z.2) ≤ (n : ℝ)
      rw [tiltedHeight_columnSlopeReflection]
      exact hstrip

/-- Horizontal reflection is an isomorphism between the two tilted square
windows, including their finite induced-edge carriers. -/
def tiltedWindowHorizontalReflectionIso (n m : ℕ) (t : ℝ) :
    (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (tiltedWindow n m (-t) : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun z => ⟨(-z.1.1,z.1.2),
        (mem_tiltedWindow_horizontalReflection n m t z.1).2 z.2⟩
      invFun := fun z => ⟨(-z.1.1,z.1.2), by
        have hz : (-z.1.1,z.1.2) ∈ tiltedWindow n m t :=
          by simpa only [neg_neg] using
            (mem_tiltedWindow_horizontalReflection n m (-t) z.1).mpr z.2
        exact hz⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro z; apply Subtype.ext; simp }
  map_rel_iff' := by
    intro u v
    change |(-u.1.1)-(-v.1.1)| + |u.1.2-v.1.2| = 1 ↔
      |u.1.1-v.1.1| + |u.1.2-v.1.2| = 1
    constructor <;> intro h <;>
      simpa only [neg_sub_neg, abs_sub_comm] using h

private theorem tiltedWindowTop_image_horizontalReflection (n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    tiltedWindowHorizontalReflectionIso n m t '' tiltedWindowWiredVertices n m t 0 =
      tiltedWindowWiredVertices n m (-t) 0 := by
  ext z
  constructor
  · rintro ⟨x,hx,hxz⟩
    have hval : (-x.1.1,x.1.2) = z.1 := congrArg Subtype.val hxz
    have htop : tiltedTop n t x.1 := by
      simpa [tiltedWindowWiredVertices] using hx
    have htarget : tiltedTop n (-t) z.1 := by
      rw [← hval]
      exact (tiltedTop_columnSlopeReflection_iff n t ht x.1).mpr htop
    simpa [tiltedWindowWiredVertices] using htarget
  · intro hz
    let e := tiltedWindowHorizontalReflectionIso n m t
    let x := e.symm z
    have hx : e x = z := by simp [x]
    have hval : (-x.1.1,x.1.2) = z.1 := congrArg Subtype.val hx
    refine ⟨x, ?_, hx⟩
    have htarget : tiltedTop n (-t) (-x.1.1,x.1.2) := by
      rw [hval]
      simpa [tiltedWindowWiredVertices] using hz
    have hsource := (tiltedTop_columnSlopeReflection_iff n t ht x.1).mp htarget
    simpa [tiltedWindowWiredVertices] using hsource

private theorem boundaryConditionIso_wired_image_horizontalReflection
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (B : Set V) :
    boundaryConditionIso e (BoundaryCondition.wired B) =
      BoundaryCondition.wired (e '' B) := by
  simp only [boundaryConditionIso, BoundaryCondition.wired]
  rw [BoundaryCondition.mk.injEq]
  constructor
  · rfl
  · apply Setoid.ext
    intro x y
    change (e.symm x = e.symm y ∨ e.symm x ∈ B ∧ e.symm y ∈ B) ↔
      (x = y ∨ x ∈ e '' B ∧ y ∈ e '' B)
    have hmem (z : W) : z ∈ e '' B ↔ e.symm z ∈ B := by
      constructor
      · rintro ⟨v,hv,rfl⟩
        simpa using hv
      · intro hz
        exact ⟨e.symm z,hz,e.apply_symm_apply z⟩
    constructor
    · rintro (h | h)
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr ⟨(hmem x).2 h.1,(hmem y).2 h.2⟩
    · rintro (h | h)
      · exact Or.inl (by simpa using congrArg e.symm h)
      · exact Or.inr ⟨(hmem x).1 h.1,(hmem y).1 h.2⟩

theorem tiltedWindowBoundary_iso_horizontalReflection (n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    boundaryConditionIso (tiltedWindowHorizontalReflectionIso n m t)
      (tiltedWindowBoundary n m t 0) = tiltedWindowBoundary n m (-t) 0 := by
  rw [tiltedWindowBoundary, boundaryConditionIso_wired_image_horizontalReflection,
    tiltedWindowTop_image_horizontalReflection n m t ht]
  rfl

/-- The top-only finite FK law is invariant under the slope reflection. -/
theorem tiltedWindowTopLaw_map_horizontalReflection (θ : Parameters) (n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (law (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))) θ
      (tiltedWindowBoundary n m t 0)).map
        (configurationIso (tiltedWindowHorizontalReflectionIso n m t)) =
      law (squareLattice.induce (tiltedWindow n m (-t) : Set (ℤ × ℤ))) θ
        (tiltedWindowBoundary n m (-t) 0) := by
  calc
    _ = law (squareLattice.induce (tiltedWindow n m (-t) : Set (ℤ × ℤ))) θ
        (boundaryConditionIso (tiltedWindowHorizontalReflectionIso n m t)
          (tiltedWindowBoundary n m t 0)) :=
      law_configurationIso_map θ (tiltedWindowHorizontalReflectionIso n m t)
        (tiltedWindowBoundary n m t 0)
    _ = _ := by rw [tiltedWindowBoundary_iso_horizontalReflection n m t ht]

end

end PottsContinuity.Thm3.Touch
