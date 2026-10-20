module

public import PottsContinuity.Thm3.Prop4.LowestHeight

/-!
# Translated tilted windows and their actual exit edges

DCST, the event A(x), TeX lines 1590–1604. A translated window is the
literal translate of the finite induced vertex set. The exit-edge dichotomy
keeps wired corners: an exit through a box side is assigned to the wired arc.
Only a lower-supporting-line exit can avoid that arc.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The literal translated finite window, represented by its inverse translation. -/
def translatedTiltedWindow (n m : ℕ) (t : ℝ) (x : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {z | z-x ∈ tiltedWindow n m t}

/-- Translate of the actual wired arc, preserving the explicit corner convention. -/
def translatedTiltedWired (n m : ℕ) (t : ℝ) (x z : ℤ × ℤ) : Prop :=
  ∃ hz : z-x ∈ tiltedWindow n m t,
    (⟨z-x,hz⟩ : (tiltedWindow n m t : Set (ℤ × ℤ))) ∈ tiltedWindowWiredVertices n m t 1

/-- Height is additive under translations, on the full lattice carrier. -/
theorem tiltedHeight_sub (t : ℝ) (z x : ℤ × ℤ) :
    tiltedHeight t (z-x) = tiltedHeight t z-tiltedHeight t x := by
  dsimp [tiltedHeight]
  push_cast
  ring

private theorem adj_sub {u v : ℤ × ℤ} (x : ℤ × ℤ) (h : squareLattice.Adj u v) :
    squareLattice.Adj (u-x) (v-x) := by
  change |(u.1-x.1)-(v.1-x.1)|+|(u.2-x.2)-(v.2-x.2)| = 1
  have hx : (u.1-x.1)-(v.1-x.1) = u.1-v.1 := by ring
  have hy : (u.2-x.2)-(v.2-x.2) = u.2-v.2 := by ring
  rw [hx,hy]
  exact h

/-- The root lies in its translated window at every radius and nonnegative height. -/
theorem mem_translatedTiltedWindow_self (n m : ℕ) (t : ℝ) (x : ℤ × ℤ) :
    x ∈ translatedTiltedWindow n m t x := by
  change x-x ∈ tiltedWindow n m t
  rw [sub_self]
  exact (tiltedWindowOrigin n m t).2

/-- Any actual exit edge either meets the wired arc, or its exterior endpoint
has lower tilted height than the root and remains within the horizontal radius. -/
theorem translatedTiltedWindow_exit_edge (n m : ℕ) (t : ℝ) (x u v : ℤ × ℤ)
    (hu : u ∈ translatedTiltedWindow n m t x)
    (hv : v ∉ translatedTiltedWindow n m t x) (huv : squareLattice.Adj u v) :
    translatedTiltedWired n m t x u ∨
      |v.1-x.1| ≤ (m : ℤ) ∧ tiltedHeight t v < tiltedHeight t x := by
  have hrelAdj := adj_sub x huv
  by_cases hvbox : v-x ∈ box m
  · have hvstrip : v-x ∉ tiltedStripVertices n t := by
      intro h
      exact hv ((mem_tiltedWindow n m t (v-x)).mpr ⟨hvbox,h⟩)
    change ¬(0 ≤ tiltedHeight t (v-x) ∧ tiltedHeight t (v-x) ≤ n) at hvstrip
    by_cases hvlow : tiltedHeight t (v-x) < 0
    · refine Or.inr ⟨?_, ?_⟩
      · exact ((Foundations.mem_box_iff_abs_le m (v-x)).mp hvbox).1
      · rw [tiltedHeight_sub] at hvlow
        exact sub_neg.mp hvlow
    · have hvhigh : (n : ℝ) < tiltedHeight t (v-x) := by
        exact lt_of_not_ge (fun h => hvstrip ⟨le_of_not_gt hvlow,h⟩)
      exact Or.inl ⟨hu, Or.inl ⟨v-x,hrelAdj,hvhigh⟩⟩
  · have hubox := ((mem_tiltedWindow n m t (u-x)).mp hu).1
    have hubd : u-x ∈ vertexBoundary (box m) := by
      rw [Foundations.vertexBoundary_eq_PD]
      exact ⟨hubox,v-x,hrelAdj,hvbox⟩
    exact Or.inl ⟨hu,Or.inr ⟨rfl,hubd⟩⟩

end PottsContinuity.Thm3.Prop4
