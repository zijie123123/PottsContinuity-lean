module

public import PottsContinuity.Thm3.Prop4.CensoredArcComparison
public import PottsContinuity.Thm3.Prop4.TouchIsolation

/-!
# Literal translated-window boundary support for the direct comparison

Intrinsic top wiring of the ambient strip can enter a lower translated window
only on that window's wired arc. The target is intersected with the ambient
truncation explicitly; no containment or large-radius case is hidden.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Target vertices of a translated window inside the actual ambient finite strip. -/
def translatedWindowDomain (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ) :
    Set (tiltedWindow N M t : Set (ℤ × ℤ)) :=
  {z | z.val ∈ translatedTiltedWindow n m t x}

/-- Its actual translated wired arc, restricted to the same ambient carrier. -/
def translatedWindowArc (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ) :
    Set (tiltedWindow N M t : Set (ℤ × ℤ)) :=
  {z | translatedTiltedWired n m t x z.val}

/-- The prescribed arc is literally part of the target induced domain. -/
theorem translatedWindowArc_subset_domain (N M n m : ℕ) (t : ℝ) (x : ℤ × ℤ) :
    translatedWindowArc N M n m t x ⊆ translatedWindowDomain N M n m t x := by
  rintro z ⟨hz,_⟩
  exact hz

/-- Ambient intrinsic-top vertices inside the target belong to its translated wired arc. -/
theorem translated_window_top_mem_arc (N n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (x z : ℤ × ℤ)
    (hxheight : tiltedHeight t x + (n : ℝ) ≤ N)
    (hzD : z ∈ translatedTiltedWindow n m t x) (hzTop : tiltedTop N t z) :
    translatedTiltedWired n m t x z := by
  refine ⟨hzD,Or.inl ?_⟩
  apply (tiltedTop_iff_height n ht (z-x)).mpr
  have h := (tiltedTop_iff_height N ht z).mp hzTop
  rw [tiltedHeight_sub]
  linarith only [hxheight,h]

/-- The actual finite intrinsic-top boundary satisfies the support hypothesis
of the unconditional isolation comparison. Artificial-side wiring is absent. -/
theorem translatedWindow_top_boundary_support (N M n m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (x : ℤ × ℤ)
    (hxheight : tiltedHeight t x + (n : ℝ) ≤ N) :
    (tiltedWindowBoundary N M t 0).boundary ⊆
      (translatedWindowDomain N M n m t x)ᶜ ∪ translatedWindowArc N M n m t x := by
  intro z hz
  have hzTop : tiltedTop N t z.val := by
    change z ∈ tiltedWindowWiredVertices N M t 0 at hz
    simpa only [tiltedWindowWiredVertices,Set.mem_ofPred_eq,Fin.zero_ne_one,false_and,or_false] using hz
  by_cases hzD : z ∈ translatedWindowDomain N M n m t x
  · exact Or.inr (translated_window_top_mem_arc N n m t ht x z.val hxheight hzD hzTop)
  · exact Or.inl hzD

/-- The direct isolation comparison specialized to genuine translated tilted
windows in every ambient truncation, at every independent FK parameter. -/
theorem translatedWindow_finite_isolation_probability_le (θ : Parameters)
    (N M n m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (x : (tiltedWindow N M t : Set (ℤ × ℤ)))
    (hxheight : tiltedHeight t x.val + (n : ℝ) ≤ N) :
    (measure (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) θ
      (tiltedWindowBoundary N M t 0)
      (finiteArcIsolationEvent (translatedWindowDomain N M n m t x.val)
        (translatedWindowArc N M n m t x.val) x)).toReal ≤
    (measure ((squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).induce
        (translatedWindowDomain N M n m t x.val)) θ
      (BoundaryCondition.wired (Subtype.val ⁻¹' translatedWindowArc N M n m t x.val))
      (targetConnectionEvent ⟨x,mem_translatedTiltedWindow_self n m t x.val⟩
        (Subtype.val ⁻¹' translatedWindowArc N M n m t x.val))).toReal :=
  finite_arc_isolation_probability_le θ _ _ (translatedWindowArc_subset_domain N M n m t x.val)
    (tiltedWindowBoundary N M t 0) (translatedWindow_top_boundary_support N M n m t ht x.val hxheight)
    ⟨x,mem_translatedTiltedWindow_self n m t x.val⟩

end
end PottsContinuity.Thm3.Prop4
