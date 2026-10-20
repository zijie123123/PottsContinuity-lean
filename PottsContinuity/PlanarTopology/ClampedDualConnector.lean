module

public import PottsContinuity.PlanarTopology.RectangleClamp
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- The actual dual walk, interpolated between face centres and projected onto
its closed primal rectangle. Every original dual edge label is retained. -/
def clampedRectangleDualCurve (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v) :
    Path (rectangleClamp a w h (dualFaceCenter unitLatticeMesh u.val))
      (rectangleClamp a w h (dualFaceCenter unitLatticeMesh v.val)) :=
  (dualWalkCurve unitLatticeMesh (q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A)))).map (continuous_rectangleClamp a w h)

/-- The connector stays in the literal closed primal rectangle. -/
theorem clampedRectangleDualCurve_mem (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v) (t : unitInterval) :
    (a.1 : ℝ) ≤ (clampedRectangleDualCurve a w h A q t).re ∧
    (clampedRectangleDualCurve a w h A q t).re ≤ (a.1 : ℝ)+w ∧
    (a.2 : ℝ) ≤ (clampedRectangleDualCurve a w h A q t).im ∧
    (clampedRectangleDualCurve a w h A q t).im ≤ (a.2 : ℝ)+h :=
  rectangleClamp_mem a w h _

/-- In a restricted trace's complementary dual, clamping does not create any
intersection with the full original walk. The nontriviality premise is an honest
walk-length condition, supplied by distinct complementary boundary ports. -/
theorem clamped_trace_dualCurve_disjoint (a : LatticeVertex) (w h : ℕ)
    {x y : LatticeVertex} (p : PD.squareLattice.Walk x y)
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h (rectangleTraceConfiguration a w h p))).Walk u v)
    (hq : 0 < q.length) :
    Disjoint (Set.range (latticeWalkPath unitLatticeMesh p))
      (Set.range (clampedRectangleDualCurve a w h (rectangleTraceConfiguration a w h p) q)) := by
  apply Set.disjoint_left.mpr
  rintro z hzP ⟨t,rfl⟩
  let Q := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h (rectangleTraceConfiguration a w h p)))
  obtain ⟨d,hd,hzD⟩ := rectangleDualWalkPath_point_on_dualBond unitLatticeMesh
    a w h (rectangleTraceConfiguration a w h p) q
    (by simpa only [SimpleGraph.Walk.length_map] using hq)
    (show dualWalkCurve unitLatticeMesh Q t ∈ Set.range (dualWalkCurve unitLatticeMesh Q)
      from ⟨t,rfl⟩)
  have hcl := rectangleClamp_dualBond_mem a w h d hzD
  exact Set.disjoint_left.mp (trace_closed_dualBond_disjoint_walk unitLatticeMesh
    a w h p d hd) hzP hcl

/-- Endpoints on the two explicit central complementary arcs are distinct. -/
theorem central_dual_ports_ne (k : ℕ) (_hk : 1 ≤ k) {b d : LatticeVertex}
    (hb : b ∈ centralLeftDualPorts k) (hd : d ∈ centralRightDualPorts k) : b ≠ d := by
  intro he
  subst d
  rcases hb with hb | hb <;> rcases hd with hd | hd <;> omega

/-- In the no-contiguous-m-path branch there is an ACTUAL continuous connector
inside H whose entire range avoids the full original piecewise-linear path.
The endpoints are exactly the projected face centres of the B/D port witnesses. -/
theorem kst_clamped_connector_of_no_mpath (k : ℕ) (hk : 1 ≤ k)
    {x y : LatticeVertex} (p : PD.squareLattice.Walk x y) (hp : p.IsPath)
    (hno : ¬∃ (u v : LatticeVertex) (r : PD.squareLattice.Walk u v),
      BD12.kstMPath (12*k) r ∧ (r.IsSubwalk p ∨ r.reverse.IsSubwalk p)) :
    ∃ b d : LatticeVertex, b ∈ centralLeftDualPorts k ∧ d ∈ centralRightDualPorts k ∧
    ∃ Q : Path
      (rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
        (dualFaceCenter unitLatticeMesh b))
      (rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
        (dualFaceCenter unitLatticeMesh d)),
      (∀ t, -13*(k : ℝ) ≤ (Q t).re ∧ (Q t).re ≤ 13*(k : ℝ) ∧
        -12*(k : ℝ) ≤ (Q t).im ∧ (Q t).im ≤ 12*(k : ℝ)) ∧
      Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) (Set.range Q) := by
  obtain ⟨b,hb,d,hd,⟨q⟩⟩ := kst_trace_dual_of_no_mpath k hk p hp hno
  have hne : b ≠ d := fun he => central_dual_ports_ne k hk hb hd (congrArg Subtype.val he)
  have hpos : 0 < q.length := by
    by_contra h
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero (p := q) (by omega))
  refine ⟨b.val,d.val,hb,hd,clampedRectangleDualCurve _ _ _ _ q,?_,
    clamped_trace_dualCurve_disjoint _ _ _ p q hpos⟩
  intro t
  have h := clampedRectangleDualCurve_mem _ _ _ _ q t
  simp only [Int.cast_mul,Int.cast_neg,Int.cast_ofNat,
    Nat.cast_mul,Nat.cast_ofNat,Int.cast_natCast] at h
  constructor
  · exact h.1
  constructor
  · linarith [h.2.1]
  constructor
  · exact h.2.2.1
  · linarith [h.2.2.2]

end
end PottsContinuity.PlanarTopology
