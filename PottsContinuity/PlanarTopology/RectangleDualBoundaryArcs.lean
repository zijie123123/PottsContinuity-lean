module

public import PottsContinuity.PlanarTopology.ClampedDualConnector
public import Mathlib.Tactic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial

/-- Actual exterior face labels on the lower arc between the left and right
primal marks. Corner faces not incident to a sampled boundary edge are excluded. -/
def rectangleLowerDualArc (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex) :
    Set LatticeVertex :=
  {s | (s.2 = a.2-1 ∧ a.1 ≤ s.1 ∧ s.1 < a.1+(w : ℤ)) ∨
    (s.1 = a.1-1 ∧ a.2 ≤ s.2 ∧ s.2 < a.2+(h : ℤ) ∧ s.2 < u.2) ∨
    (s.1 = a.1+(w : ℤ) ∧ a.2 ≤ s.2 ∧ s.2 < a.2+(h : ℤ) ∧ s.2 < v.2)}

/-- Actual exterior face labels on the upper complementary arc. -/
def rectangleUpperDualArc (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex) :
    Set LatticeVertex :=
  {s | (s.2 = a.2+(h : ℤ) ∧ a.1 ≤ s.1 ∧ s.1 < a.1+(w : ℤ)) ∨
    (s.1 = a.1-1 ∧ a.2 ≤ s.2 ∧ u.2 ≤ s.2 ∧ s.2 < a.2+(h : ℤ)) ∨
    (s.1 = a.1+(w : ℤ) ∧ a.2 ≤ s.2 ∧ v.2 ≤ s.2 ∧ s.2 < a.2+(h : ℤ))}

/-- The two complementary exterior arcs have no common original face label. -/
theorem rectangle_lower_upper_dual_arcs_disjoint (a : LatticeVertex) (w h : ℕ)
    (u v : LatticeVertex) : Disjoint (rectangleLowerDualArc a w h u v)
      (rectangleUpperDualArc a w h u v) := by
  apply Set.disjoint_left.mpr
  intro s hs ht
  rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;> omega

/-- Clamping a genuine lower exterior label gives the correct lower boundary
arc, cut at the two respective original primal endpoint heights. -/
theorem rectangle_lower_dual_arc_clamped (a : LatticeVertex) (w h : ℕ)
    (u v s : LatticeVertex) (hs : s ∈ rectangleLowerDualArc a w h u v) :
    let z := rectangleClamp a w h (dualFaceCenter unitLatticeMesh s)
    z.im = (a.2 : ℝ) ∨ (z.re = (a.1 : ℝ) ∧ z.im < (u.2 : ℝ)) ∨
      (z.re = (a.1 : ℝ)+w ∧ z.im < (v.2 : ℝ)) := by
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hx : (dualFaceCenter unitLatticeMesh s).re = (s.1 : ℝ)+1/2 := by
    simp [dualFaceCenter,latticeEmbed,unitLatticeMesh]
  have hy : (dualFaceCenter unitLatticeMesh s).im = (s.2 : ℝ)+1/2 := by
    simp [dualFaceCenter,latticeEmbed,unitLatticeMesh]
  dsimp only
  rcases hs with ⟨hs,_,_⟩ | ⟨hs,hs0,_,hsu⟩ | ⟨hs,hs0,_,hsv⟩
  · left
    change max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _) = _
    rw [hy]
    have he : (s.2 : ℝ) = (a.2 : ℝ)-1 := by exact_mod_cast hs
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · right; left
    constructor
    · change max (a.1 : ℝ) (min ((a.1 : ℝ)+w) _) = _
      rw [hx]
      have he : (s.1 : ℝ) = (a.1 : ℝ)-1 := by exact_mod_cast hs
      exact max_eq_left ((min_le_right _ _).trans (by linarith))
    · change max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _) < (u.2 : ℝ)
      rw [hy]
      have hl : (a.2 : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast hs0
      have hu : (s.2 : ℝ)+1 ≤ (u.2 : ℝ) := by exact_mod_cast (show s.2+1 ≤ u.2 by omega)
      exact max_lt (by linarith) ((min_le_right _ _).trans_lt (by linarith))
  · right; right
    constructor
    · change max (a.1 : ℝ) (min ((a.1 : ℝ)+w) _) = _
      rw [hx]
      have he : (s.1 : ℝ) = (a.1 : ℝ)+w := by exact_mod_cast hs
      rw [min_eq_left (by linarith),max_eq_right (by linarith)]
    · change max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _) < (v.2 : ℝ)
      rw [hy]
      have hl : (a.2 : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast hs0
      have hv : (s.2 : ℝ)+1 ≤ (v.2 : ℝ) := by exact_mod_cast (show s.2+1 ≤ v.2 by omega)
      exact max_lt (by linarith) ((min_le_right _ _).trans_lt (by linarith))

/-- The upper exterior face labels clamp to the actual upper complementary arc. -/
theorem rectangle_upper_dual_arc_clamped (a : LatticeVertex) (w h : ℕ)
    (u v s : LatticeVertex) (hs : s ∈ rectangleUpperDualArc a w h u v) :
    let z := rectangleClamp a w h (dualFaceCenter unitLatticeMesh s)
    z.im = (a.2 : ℝ)+h ∨ (z.re = (a.1 : ℝ) ∧ (u.2 : ℝ) < z.im) ∨
      (z.re = (a.1 : ℝ)+w ∧ (v.2 : ℝ) < z.im) := by
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hx : (dualFaceCenter unitLatticeMesh s).re = (s.1 : ℝ)+1/2 := by
    simp [dualFaceCenter,latticeEmbed,unitLatticeMesh]
  have hy : (dualFaceCenter unitLatticeMesh s).im = (s.2 : ℝ)+1/2 := by
    simp [dualFaceCenter,latticeEmbed,unitLatticeMesh]
  dsimp only
  rcases hs with ⟨hs,_,_⟩ | ⟨hs,_,hus,hst⟩ | ⟨hs,_,hvs,hst⟩
  · left
    change max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _) = _
    rw [hy]
    have he : (s.2 : ℝ) = (a.2 : ℝ)+h := by exact_mod_cast hs
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]
  · right; left
    constructor
    · change max (a.1 : ℝ) (min ((a.1 : ℝ)+w) _) = _
      rw [hx]
      have he : (s.1 : ℝ) = (a.1 : ℝ)-1 := by exact_mod_cast hs
      exact max_eq_left ((min_le_right _ _).trans (by linarith))
    · change (u.2 : ℝ) < max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _)
      rw [hy]
      have hu : (u.2 : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast hus
      have ht : (s.2 : ℝ)+1 ≤ (a.2 : ℝ)+h := by exact_mod_cast (show s.2+1 ≤ a.2+(h : ℤ) by omega)
      exact (lt_min (by linarith) (by linarith)).trans_le (le_max_right _ _)
  · right; right
    constructor
    · change max (a.1 : ℝ) (min ((a.1 : ℝ)+w) _) = _
      rw [hx]
      have he : (s.1 : ℝ) = (a.1 : ℝ)+w := by exact_mod_cast hs
      rw [min_eq_left (by linarith),max_eq_right (by linarith)]
    · change (v.2 : ℝ) < max (a.2 : ℝ) (min ((a.2 : ℝ)+h) _)
      rw [hy]
      have hv : (v.2 : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast hvs
      have ht : (s.2 : ℝ)+1 ≤ (a.2 : ℝ)+h := by exact_mod_cast (show s.2+1 ≤ a.2+(h : ℤ) by omega)
      exact (lt_min (by linarith) (by linarith)).trans_le (le_max_right _ _)

end PottsContinuity.PlanarTopology
