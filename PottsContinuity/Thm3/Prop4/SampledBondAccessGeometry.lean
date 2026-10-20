module

public import PottsContinuity.PlanarTopology.RectangleClamp
public import PottsContinuity.PlanarTopology.OccurrenceDualHalfSegments
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-! # Actual midpoint access for original sampled rectangle bonds -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology
noncomputable section

/-- The shared face-center midpoint identity transported to the PD carrier. -/
theorem pd_bond_midpoint_eq_dual_midpoint (δ : PositiveMesh) (b : LatticeBond) :
    b.midpoint δ = midpoint ℝ (dualFaceCenter δ (dualBondOfPrimal b).source)
      (dualFaceCenter δ (dualBondOfPrimal b).target) := by
  rcases b with ⟨base,axis⟩
  cases axis with
  | horizontal => exact PlanarTopology.bond_midpoint_eq_dual_midpoint δ ⟨base,.horizontal⟩
  | vertical => exact PlanarTopology.bond_midpoint_eq_dual_midpoint δ ⟨base,.vertical⟩

/-- Every point of an original primal bond stays inside its literal rectangle. -/
theorem sampled_primal_bond_segment_bounds (a : LatticeVertex) (w h : ℕ)
    (b : RectanglePrimalBond a w h) {z : ℂ}
    (hz : z ∈ primalBondSegment unitLatticeMesh b.val) :
    (a.1 : ℝ) ≤ z.re ∧ z.re ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.im ∧ z.im ≤ (a.2 : ℝ)+h := by
  let S : Set ℂ := Complex.re ⁻¹' Set.Icc (a.1 : ℝ) ((a.1 : ℝ)+w) ∩
    Complex.im ⁻¹' Set.Icc (a.2 : ℝ) ((a.2 : ℝ)+h)
  have hS : Convex ℝ S :=
    ((convex_Icc _ _).affine_preimage Complex.reLm.toAffineMap).inter
      ((convex_Icc _ _).affine_preimage Complex.imLm.toAffineMap)
  have hb (x : LatticeVertex) (hx : x ∈ latticeRectangle a w h) :
      latticeEmbed unitLatticeMesh x ∈ S := by
    have hh := (mem_latticeRectangle a x w h).mp hx
    change ((a.1 : ℝ) ≤ (latticeEmbed unitLatticeMesh x).re ∧
      (latticeEmbed unitLatticeMesh x).re ≤ (a.1 : ℝ)+w) ∧
      ((a.2 : ℝ) ≤ (latticeEmbed unitLatticeMesh x).im ∧
      (latticeEmbed unitLatticeMesh x).im ≤ (a.2 : ℝ)+h)
    simp only [latticeEmbed_re,latticeEmbed_im,unitLatticeMesh,one_mul]
    exact_mod_cast hh
  have hh := hS.segment_subset (hb _ b.property.1) (hb _ b.property.2) hz
  exact ⟨hh.1.1,hh.1.2,hh.2.1,hh.2.2⟩

/-- Coordinate projection fixes every point already in the original rectangle. -/
theorem rectangleClamp_eq_self_of_bounds (a : LatticeVertex) (w h : ℕ) (z : ℂ)
    (hz : (a.1 : ℝ) ≤ z.re ∧ z.re ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ) ≤ z.im ∧ z.im ≤ (a.2 : ℝ)+h) : rectangleClamp a w h z = z := by
  apply Complex.ext
  · exact (congrArg (max (a.1 : ℝ)) (min_eq_right hz.2.1)).trans (max_eq_right hz.1)
  · exact (congrArg (max (a.2 : ℝ)) (min_eq_right hz.2.2.2)).trans (max_eq_right hz.2.2.1)

/-- The actual midpoint of a sampled primal bond is on its crossing dual bond. -/
theorem sampled_bond_midpoint_mem_crossing_segment (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e.primalEdge).midpoint unitLatticeMesh ∈
      dualBondSegment unitLatticeMesh e.crossingBond := by
  rw [e.crossingBond_eq,rectangleCrossingDualBond,pd_bond_midpoint_eq_dual_midpoint]
  exact midpoint_mem_segment _ _

end
end PottsContinuity.Thm3.Prop4
