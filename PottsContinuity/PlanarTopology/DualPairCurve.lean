module

public import PottsContinuity.PlanarTopology.KSTCurveIntersection
public import PottsContinuity.PlanarTopology.WholePlaneWalkExclusion
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- Unit-mesh dual interpolation in real coordinates, including half-cell offsets. -/
def dualPairCurve {u v : LatticeVertex} (q : PD.squareLattice.Walk u v) :
    Path ((u.1 : ℝ)+1/2,(u.2 : ℝ)+1/2) ((v.1 : ℝ)+1/2,(v.2 : ℝ)+1/2) :=
  ((dualWalkCurve unitLatticeMesh q).map continuous_complexCoordinates).cast
    (by simp [complexCoordinates,dualFaceCenter,latticeEmbed,unitLatticeMesh])
    (by simp [complexCoordinates,dualFaceCenter,latticeEmbed,unitLatticeMesh])

private theorem complex_segment_box {a b z : ℂ} {l r d t : ℝ}
    (ha : l ≤ a.re ∧ a.re ≤ r ∧ d ≤ a.im ∧ a.im ≤ t)
    (hb : l ≤ b.re ∧ b.re ≤ r ∧ d ≤ b.im ∧ b.im ≤ t)
    (hz : z ∈ Set.range (Path.segment a b)) :
    l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ t := by
  rw [Path.range_segment,segment_eq_image] at hz
  obtain ⟨θ,hθ,rfl⟩ := hz
  simp only [Complex.add_re,Complex.add_im,Complex.real_smul,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  exact ⟨by nlinarith [ha.1,hb.1,hθ.1,hθ.2],by nlinarith [ha.2.1,hb.2.1,hθ.1,hθ.2],
    by nlinarith [ha.2.2.1,hb.2.2.1,hθ.1,hθ.2],by nlinarith [ha.2.2.2,hb.2.2.2,hθ.1,hθ.2]⟩

/-- Face-centre bounds on original support vertices bound the entire dual curve. -/
theorem dualPairCurve_bounds {u v : LatticeVertex} (q : PD.squareLattice.Walk u v)
    (hq : 0 < q.length) {l r b t : ℝ}
    (hbox : ∀ z ∈ q.support,
      l ≤ (z.1 : ℝ)+1/2 ∧ (z.1 : ℝ)+1/2 ≤ r ∧ b ≤ (z.2 : ℝ)+1/2 ∧ (z.2 : ℝ)+1/2 ≤ t) :
    ∀ θ, l ≤ (dualPairCurve q θ).1 ∧ (dualPairCurve q θ).1 ≤ r ∧
      b ≤ (dualPairCurve q θ).2 ∧ (dualPairCurve q θ).2 ≤ t := by
  intro θ
  obtain ⟨x,y,hx,hy,_,_,hseg⟩ := dualWalkCurve_range_actual_segment unitLatticeMesh q hq
    (show dualWalkCurve unitLatticeMesh q θ ∈ Set.range (dualWalkCurve unitLatticeMesh q) from ⟨θ,rfl⟩)
  have hc (z : LatticeVertex) (hz : z ∈ q.support) :
      l ≤ (dualFaceCenter unitLatticeMesh z).re ∧ (dualFaceCenter unitLatticeMesh z).re ≤ r ∧
      b ≤ (dualFaceCenter unitLatticeMesh z).im ∧ (dualFaceCenter unitLatticeMesh z).im ≤ t := by
    simpa [dualFaceCenter,latticeEmbed,unitLatticeMesh] using hbox z hz
  exact complex_segment_box (hc x hx) (hc y hy) hseg

/-- Complementary original primal and dual curves remain disjoint in real coordinates. -/
theorem latticePairCurve_dualPairCurve_disjoint (ω : LatticeConfiguration)
    {u v x y : LatticeVertex} (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    (hp : BD12.kstPathOpen ω p)
    (hq : BD12.kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (hpne : 0 < p.length) (hqne : 0 < q.length) :
    Disjoint (Set.range (latticePairCurve p)) (Set.range (dualPairCurve q)) :=
  latticePairCurve_disjoint p (dualWalkCurve unitLatticeMesh q)
    (wholePlane_open_dual_curves_disjoint unitLatticeMesh ω p q hp hq hpne hqne)

end
end PottsContinuity.PlanarTopology
