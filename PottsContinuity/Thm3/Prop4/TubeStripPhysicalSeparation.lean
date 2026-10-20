module

public import PottsContinuity.Thm3.Prop4.TubeStripPhysicalCrop

/-!
# Physical first exits and the widened tilted-window target

The physical face layer separates every cropped strip walk from its exterior.
At scale 4n+2 the original wired top and truncation sides are all outside the
physical crop, uniformly in both frames and every physical vertical root.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

private theorem physical_exit_mem_dual_boundary (n : ℕ) (x y : LatticeVertex)
    (hx : x ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hxy : squareLattice.Adj x y)
    (hy : y ∉ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    x ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
  refine Finset.mem_filter.mpr ⟨hx,?_⟩
  intro hinside
  have hi := (Finset.mem_filter.mp hinside).2
  apply hy
  rw [rectangleDualExpanded,mem_latticeRectangle]
  have hxyPD : PD.FK.squareLattice.Adj x y := hxy
  rw [PD.FK.squareLattice_adj_iff] at hxyPD
  dsimp at hi ⊢
  omega

/-- Leaving the physical crop along a genuine strip edge starts at its
physical exterior face layer. -/
theorem tubeStripPhysicalSeparator_is_separator (n N M : ℕ) (t : ℝ) (c : ℤ) (reflected : Bool)
    (x : (tiltedWindow N M t : Set LatticeVertex)) (hx : x ∈ tubeStripPhysicalCrop n N M t c reflected)
    (y : (tiltedWindow N M t : Set LatticeVertex))
    (hxy : (squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)).Adj x y)
    (hy : y ∉ tubeStripPhysicalCrop n N M t c reflected) :
    x ∈ tubeStripPhysicalSeparator n N M t c reflected := by
  apply physical_exit_mem_dual_boundary n _ _ hx _ hy
  exact (tubeStripFrame c reflected).map_rel_iff.mpr hxy

/-- Every physically permitted vertical root is in the literal crop. -/
theorem tiltedWindowOrigin_mem_physicalCrop (n N M : ℕ) (t : ℝ) (c : ℤ)
    (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool) :
    tiltedWindowOrigin N M t ∈ tubeStripPhysicalCrop n N M t c reflected := by
  change tubeStripFrame c reflected (0,0) ∈ rectangleDualExpanded _ _ _
  rw [rectangleDualExpanded,mem_latticeRectangle]
  cases reflected <;> dsimp [tubeStripFrame]<;> omega

/-- At the widened scale, every designated wired vertex lies outside the
physical crop. The intrinsic digital top and artificial sides are both covered. -/
theorem widened_tilted_wired_target_outside_physicalCrop {n : ℕ} (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (c : ℤ)
    (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool) :
    tiltedWindowWiredVertices (4*n+2) (4*n+2) t 1 ⊆
      (tubeStripPhysicalCrop n (4*n+2) (4*n+2) t c reflected)ᶜ := by
  intro z hz hzcrop
  have hb := tubeStripPhysicalCrop_coordinate_bounds n (4*n+2) (4*n+2) t c hc reflected z hzcrop
  rcases hz with htop | ⟨_,hside⟩
  · have hx : |(z.val.1 : ℝ)| ≤ (n : ℝ)+1 := by exact_mod_cast hb.1
    have hy : |(z.val.2 : ℝ)| ≤ 2*(n : ℝ)+1 := by exact_mod_cast hb.2
    have htAbs : |t| ≤ 1 := abs_le.mpr ht
    have hm : |t*(z.val.1 : ℝ)| ≤ |(z.val.1 : ℝ)| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right htAbs (abs_nonneg (z.val.1 : ℝ))
    have h1 := le_abs_self (z.val.2 : ℝ)
    have h2 := neg_le_abs (t*(z.val.1 : ℝ))
    have hheight : tiltedHeight t z.val ≤ 3*(n : ℝ)+2 := by
      dsimp [tiltedHeight]
      linarith only [hx,hy,hm,h1,h2]
    have htop' := (tiltedTop_iff_height (4*n+2) ht z.val).mp htop
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at htop'
    linarith only [htop',hheight,hnR]
  · rw [Foundations.vertexBoundary_box_eq] at hside
    change max |z.val.1| |z.val.2| = ((4*n+2 : ℕ) : ℤ) at hside
    have hmax : max |z.val.1| |z.val.2| ≤ 2*(n : ℤ)+1 :=
      max_le (hb.1.trans (by omega)) hb.2
    push_cast at hside
    omega

end PottsContinuity.Thm3.Prop4
