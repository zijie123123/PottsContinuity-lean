module

public import PottsContinuity.Thm3.Prop4.TubeWidth
public import PottsContinuity.Frozen.Defs

/-!
# The Euclidean/square-radius issue in the split-at-z step

Source lines 1695–1709 infer square-arm cutoffs from Euclidean distance to
[u,v]. This module verifies a concrete failure of the underlying same-radius
geometric implication.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A universally valid coarse conversion from Euclidean tube distance to square radius. -/
theorem tubeDistance_le_twice_endpoint_radius (u v z : ℤ × ℤ) :
    tubeDistance u v z ≤ 2*(max |z.1-u.1| |z.2-u.2| : ℤ) := by
  have hnorm := Complex.norm_le_abs_re_add_abs_im (tubeLatticePoint z-tubeLatticePoint u)
  have hdist := Metric.infDist_le_dist_of_mem
    (x := tubeLatticePoint z) (left_mem_segment ℝ (tubeLatticePoint u) (tubeLatticePoint v))
  rw [dist_eq_norm] at hdist
  change tubeDistance u v z ≤ _ at hdist
  have hx : |(z.1 : ℝ)-(u.1 : ℝ)| ≤ (max |z.1-u.1| |z.2-u.2| : ℤ) := by
    exact_mod_cast le_max_left |z.1-u.1| |z.2-u.2|
  have hy : |(z.2 : ℝ)-(u.2 : ℝ)| ≤ (max |z.1-u.1| |z.2-u.2| : ℤ) := by
    exact_mod_cast le_max_right |z.1-u.1| |z.2-u.2|
  change ‖tubeLatticePoint z-tubeLatticePoint u‖ ≤
    |(z.1 : ℝ)-(u.1 : ℝ)|+|(z.2 : ℝ)-(u.2 : ℝ)| at hnorm
  linarith only [hdist,hnorm,hx,hy]

/-- Removing the last edge can lose one unit of square radius. -/
theorem endpoint_radius_neighbour_step (u z a : ℤ × ℤ) (hza : squareLattice.Adj z a) :
    max |z.1-u.1| |z.2-u.2| ≤ max |a.1-u.1| |a.2-u.2|+1 := by
  change |z.1-a.1|+|z.2-a.2|=1 at hza
  simp only [abs_eq_max_neg] at hza ⊢
  omega

/-- Corrected radius r/2-1 for a neighbour of a point at Euclidean distance ≥r. -/
theorem splitRadius_neighbour_cutoff_corrected (u v z a : ℤ × ℤ) (r : ℝ)
    (hfar : r ≤ tubeDistance u v z) (hza : squareLattice.Adj z a) :
    r/2-1 ≤ (max |a.1-u.1| |a.2-u.2| : ℤ) := by
  have hgeom := tubeDistance_le_twice_endpoint_radius u v z
  have hstep : ((max |z.1-u.1| |z.2-u.2| : ℤ) : ℝ) ≤
      ((max |a.1-u.1| |a.2-u.2| : ℤ) : ℝ)+1 := by
    exact_mod_cast endpoint_radius_neighbour_step u z a hza
  linarith only [hfar,hgeom,hstep]

/-- A tube of radius 4r restores the desired square-arm cutoff r at every r≥1. -/
theorem splitRadius_neighbour_cutoff_of_widenedTube (u v z a : ℤ × ℤ) (r : ℝ)
    (hr : 1 ≤ r) (hfar : 4*r ≤ tubeDistance u v z) (hza : squareLattice.Adj z a) :
    r ≤ (max |a.1-u.1| |a.2-u.2| : ℤ) := by
  have h := splitRadius_neighbour_cutoff_corrected u v z a (4*r) hfar hza
  linarith only [h,hr]

end PottsContinuity.Thm3.Prop4
