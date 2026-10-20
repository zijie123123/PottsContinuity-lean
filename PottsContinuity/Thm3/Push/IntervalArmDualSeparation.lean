module

public import PottsContinuity.Thm3.Push.IntervalArmCurveIntersection
public import PottsContinuity.Thm3.Push.IntervalArmDualPorts
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
open PottsContinuity.PlanarTopology
noncomputable section

/-- An actual open arm from the bottom interval to any point of the top
prevents a complementary closed-dual path joining the two exterior arcs. -/
theorem interval_arm_excludes_complementary_dual_connection
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    {b d : RectangleDualVertex (0,0) N N}
    (hb : b ∈ intervalArmLeftDualPorts N l) (hd : d ∈ intervalArmRightDualPorts N r) :
    ¬ ActualConnected (rectangleDualGraph (0,0) N N)
      (rectangleDualConfiguration (0,0) N N A) b d := by
  intro hconn
  obtain ⟨q⟩ := hconn
  have hbC := interval_arm_left_port_clamped N l hl b hb
  have hdC := interval_arm_right_port_clamped N r hr d hd
  have hlrR : (l : ℝ) ≤ r := by exact_mod_cast hlr
  have hbd : b ≠ d := by
    intro he
    subst d
    linarith [hbC.1,hdC.1]
  have hq : 0 < q.length := Nat.pos_of_ne_zero (fun h => hbd (q.eq_of_length_eq_zero h))
  let P := p.map (rectangleOpenGraphToSquare (0,0) N N A)
  let Q := clampedRectangleDualCurve (0,0) N N A q
  have hP : ∀ z ∈ Set.range (latticePairCurve P),
      (0 : ℝ) ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N := by
    apply latticePairCurve_bounds
    intro z hz
    have hz' : z ∈ p.support.map (fun v : RectangleVertex (0,0) N N => v.val) := by
      simpa [P,SimpleGraph.Walk.support_map,rectangleOpenGraphToSquare] using hz
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz'
    have hv := v.property
    rw [mem_latticeRectangle] at hv
    simp only [zero_add] at hv
    exact ⟨by exact_mod_cast hv.1.1,by exact_mod_cast hv.1.2,
      by exact_mod_cast hv.2.1,by exact_mod_cast hv.2.2⟩
  have hQ : ∀ z ∈ Set.range (Q.map continuous_complexCoordinates),
      (0 : ℝ) ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N := by
    rintro z ⟨θ,rfl⟩
    change 0 ≤ (Q θ).re ∧ (Q θ).re ≤ N ∧ 0 ≤ (Q θ).im ∧ (Q θ).im ≤ N
    have h := clampedRectangleDualCurve_mem (0,0) N N A q θ
    simpa only [Q,Int.cast_zero,zero_add] using h
  have hx : (complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh b.val))).1 < (s.val.1 : ℝ) ∧
      ((complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh b.val))).1 = 0 ∨
       (complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh b.val))).2 = 0) :=
    ⟨hbC.1.trans_le (by exact_mod_cast hsl),hbC.2⟩
  have hsrR : (s.val.1 : ℝ) ≤ r := by exact_mod_cast hsr
  have hy : (s.val.1 : ℝ) < (complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh d.val))).1 ∧
      ((complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh d.val))).1 = N ∨
       (complexCoordinates (rectangleClamp (0,0) N N
        (dualFaceCenter unitLatticeMesh d.val))).2 = 0) :=
    ⟨hsrR.trans_lt hdC.1,hdC.2⟩
  obtain ⟨z,hzP,hzQ⟩ := interval_arm_complementary_curves_intersect 0 N 0 N
    (latticePairCurve P) (Q.map continuous_complexCoordinates) hP hQ
    (by change (s.val.2 : ℝ) = 0; exact_mod_cast hs)
    (by change (t.val.2 : ℝ) = N; exact_mod_cast ht) hx hy
  have hdis := latticePairCurve_disjoint P Q
    (clamped_dualCurve_disjoint_of_trace_subset (0,0) N N A P
      (rectangle_open_walk_trace_subset (0,0) N N A p) q hq)
  exact Set.disjoint_left.mp hdis hzP hzQ

end
end PottsContinuity.Push
