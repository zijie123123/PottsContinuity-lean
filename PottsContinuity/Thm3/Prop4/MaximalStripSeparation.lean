module

public import PottsContinuity.Thm3.Prop4.MaximalStripCrop

/-!
# First exits and wired targets for a strip at an arbitrary physical root

The widened local scale leaves every wired strip vertex outside the actual
expanded rectangle. Every step out of the crop starts on its true face layer.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- An actual strip edge leaving the physical crop starts at the physical
exterior face layer, also at a corner of that rectangle. -/
theorem maximalStripSeparator_is_separator (n N M : ℕ) (t : ℝ) (z : LatticeVertex)
    (x : (tiltedWindow N M t : Set LatticeVertex)) (hx : x ∈ maximalStripCrop n N M t z)
    (y : (tiltedWindow N M t : Set LatticeVertex))
    (hxy : (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)).Adj x y)
    (hy : y ∉ maximalStripCrop n N M t z) : x ∈ maximalStripSeparator n N M t z := by
  refine Finset.mem_filter.mpr ⟨hx,?_⟩
  intro hinside
  have hi := (Finset.mem_filter.mp hinside).2
  apply hy
  change latticeTranslate z y.val ∈ rectangleDualExpanded _ _ _
  rw [rectangleDualExpanded,mem_latticeRectangle]
  have hadj := (latticeTranslationIso z).map_rel_iff.mpr hxy
  change PD.FK.squareLattice.Adj (latticeTranslate z x.val) (latticeTranslate z y.val) at hadj
  rw [squareLattice_adj_iff] at hadj
  dsimp at hi hadj ⊢
  omega

/-- At scale 4n+4 all intrinsic top and truncation-side wired vertices lie
outside the crop, uniformly over every root in the expanded rectangle. -/
theorem maximalStrip_wired_target_outside_crop (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    tiltedWindowWiredVertices (4*n+4) (4*n+4) t 1 ⊆
      (maximalStripCrop n (4*n+4) (4*n+4) t z)ᶜ := by
  intro w hw hwcrop
  have hb := maximalStripCrop_coordinate_bounds n (4*n+4) (4*n+4) t z hz w hwcrop
  rcases hw with htop | ⟨_,hside⟩
  · have hx : |(w.val.1 : ℝ)| ≤ 2*(n : ℝ)+1 := by exact_mod_cast hb.1
    have hy : |(w.val.2 : ℝ)| ≤ 2*(n : ℝ)+1 := by exact_mod_cast hb.2
    have hm : |t*(w.val.1 : ℝ)| ≤ |(w.val.1 : ℝ)| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (abs_le.mpr ht)
        (abs_nonneg (w.val.1 : ℝ))
    have h1 := le_abs_self (w.val.2 : ℝ)
    have h2 := neg_le_abs (t*(w.val.1 : ℝ))
    have hheight : tiltedHeight t w.val ≤ 4*(n : ℝ)+2 := by
      dsimp [tiltedHeight]
      linarith only [hx,hy,hm,h1,h2]
    have htop' := (tiltedTop_iff_height (4*n+4) ht w.val).mp htop
    push_cast at htop'
    linarith only [htop',hheight]
  · rw [Foundations.vertexBoundary_box_eq] at hside
    change max |w.val.1| |w.val.2| = ((4*n+4 : ℕ) : ℤ) at hside
    have hmax := max_le hb.1 hb.2
    push_cast at hside
    omega

end PottsContinuity.Thm3.Prop4
