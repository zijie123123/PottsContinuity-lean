module

public import PottsContinuity.Thm3.Prop4.MarkedRectangleRawAccess
public import PottsContinuity.PlanarTopology.RectangleClamp

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology
noncomputable section

theorem dualFaceCenter_endpoint_coordinate_bounds (e : LatticeBond)
    (x f : LatticeVertex) (hx : x = e.source ∨ x = e.target)
    (hf : f = (dualBondOfPrimal e).source ∨ f = (dualBondOfPrimal e).target) :
    |(dualFaceCenter unitLatticeMesh f).re - (x.1 : ℝ)| ≤ 1/2 ∧
    |(dualFaceCenter unitLatticeMesh f).im - (x.2 : ℝ)| ≤ 1/2 := by
  rcases e with ⟨⟨a,b⟩,axis⟩
  cases axis <;> rcases hx with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num [dualBondOfPrimal,LatticeBond.source,LatticeBond.target,
      dualFaceCenter,latticeEmbed,unitLatticeMesh] <;> ring_nf <;> norm_num

theorem clamp_coordinate_distance_le {l r x y D : ℝ}
    (hl : l ≤ x) (hr : x ≤ r) (hxy : |y-x| ≤ D) :
    |max l (min r y)-x| ≤ D := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hxy
  apply abs_le.mpr
  constructor
  · have hc : x-D ≤ max l (min r y) :=
      (le_min (by linarith) (by linarith)).trans (le_max_right _ _)
    linarith
  · have hc : max l (min r y) ≤ x+D :=
      max_le (by have := abs_nonneg (y-x); linarith) ((min_le_right _ _).trans (by linarith))
    linarith

/-- Clamping the actual adjacent dual face changes affine height by at most
one when the supporting slope has absolute value at most one. -/
theorem rectangleClampedFace_endpoint_height_distance_le
    (a : LatticeVertex) (w h : ℕ) (d : RectangleDualEdgeCarrier a w h)
    (x : RectangleVertex a w h) (hx : x ∈ d.primalEdge.val)
    (f : LatticeVertex) (hf : f = d.crossingBond.source ∨ f = d.crossingBond.target)
    (t b : ℝ) (ht : |t| ≤ 1) :
    |((rectangleClamp a w h (dualFaceCenter unitLatticeMesh f)).im -
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh f)).re+b)) -
      ((x.val.2 : ℝ)-(t*x.val.1+b))| ≤ 1 := by
  have he := rectangle_edge_vertex_normalized_endpoint a w h d.primalEdge x hx
  have hf' : f = (dualBondOfPrimal (rectanglePrimalEdgeBond a w h d.primalEdge)).source ∨
      f = (dualBondOfPrimal (rectanglePrimalEdgeBond a w h d.primalEdge)).target := by
    simpa only [d.crossingBond_eq,rectangleCrossingDualBond] using hf
  obtain ⟨hxr,hyi⟩ := dualFaceCenter_endpoint_coordinate_bounds _ x.val f he hf'
  obtain ⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩ := (mem_latticeRectangle a x.val w h).mp x.property
  have hxr' := clamp_coordinate_distance_le (show (a.1 : ℝ) ≤ (x.val.1 : ℝ) by exact_mod_cast hx0)
    (show (x.val.1 : ℝ) ≤ (a.1 : ℝ)+w by exact_mod_cast hx1) hxr
  have hyi' := clamp_coordinate_distance_le (show (a.2 : ℝ) ≤ (x.val.2 : ℝ) by exact_mod_cast hy0)
    (show (x.val.2 : ℝ) ≤ (a.2 : ℝ)+h by exact_mod_cast hy1) hyi
  change |(_ - (t*_+b))-((x.val.2 : ℝ)-(t*x.val.1+b))| ≤ 1
  let z := rectangleClamp a w h (dualFaceCenter unitLatticeMesh f)
  change |(z.im-(t*z.re+b))-((x.val.2 : ℝ)-(t*x.val.1+b))| ≤ 1
  have hr : |z.re-(x.val.1 : ℝ)| ≤ 1/2 := hxr'
  have hi : |z.im-(x.val.2 : ℝ)| ≤ 1/2 := hyi'
  calc
    _ = |(z.im-(x.val.2 : ℝ))-t*(z.re-(x.val.1 : ℝ))| := by congr 1; ring
    _ ≤ |z.im-(x.val.2 : ℝ)|+|t*(z.re-(x.val.1 : ℝ))| := by simpa using abs_sub_le (z.im-(x.val.2 : ℝ)) 0 (t*(z.re-(x.val.1 : ℝ)))
    _ ≤ 1/2 + 1*(1/2) := add_le_add hi (by
      rw [abs_mul]
      exact mul_le_mul ht hr (abs_nonneg _) (by norm_num))
    _ = 1 := by norm_num

end
end PottsContinuity.Thm3.Prop4
