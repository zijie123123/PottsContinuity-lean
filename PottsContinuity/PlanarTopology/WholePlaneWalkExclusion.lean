module

public import PottsContinuity.PlanarTopology.DualWalkCurves
public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves BD12
noncomputable section

/-- Positive-length original open primal and complementary dual walks have
 disjoint interpolated traces, with their actual edge labels retained. -/
theorem wholePlane_open_dual_curves_disjoint (δ : PositiveMesh)
    (ω : LatticeConfiguration) {u v x y : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    (hp : kstPathOpen ω p)
    (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (hpne : 0 < p.length) (hqne : 0 < q.length) :
    Disjoint (Set.range (latticeWalkPath δ p)) (Set.range (dualWalkCurve δ q)) := by
  apply Set.disjoint_left.mpr
  intro z hzP hzQ
  obtain ⟨a,b,_,_,he,habe,hsegP⟩ := latticeWalkPath_range_actual_segment δ p hpne hzP
  obtain ⟨c,d,_,_,hf,hcde,hsegQ⟩ := dualWalkCurve_range_actual_segment δ q hqne hzQ
  let B := wholePlaneBondEdgeEquiv.symm ⟨s(a,b),habe⟩
  let D := wholePlaneBondEdgeEquiv.symm ⟨s(c,d),hcde⟩
  have hB : B.toSym2 = s(a,b) := congrArg Subtype.val
    (wholePlaneBondEdgeEquiv.apply_symm_apply ⟨s(a,b),habe⟩)
  have hD : D.toSym2 = s(c,d) := congrArg Subtype.val
    (wholePlaneBondEdgeEquiv.apply_symm_apply ⟨s(c,d),hcde⟩)
  have hcross := (primalDualSegments_intersect_iff δ B D).mp
    ⟨z,latticeSegment_subset_primalBond δ B hB hsegP,dualCenterSegment_subset_label δ D hD hsegQ⟩
  have hprimal : primalBondOfDual D = B := by
    rw [hcross,primalBondOfDual_dualBondOfPrimal]
  have hoP : latticeConfigurationBondState ω B = true := by
    change ω (wholePlaneBondEdgeEquiv B) = true
    rw [wholePlaneBondEdgeEquiv.apply_symm_apply]
    exact hp _ he
  have hoQ : latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω) D = true := by
    change wholePlaneDualConfigurationHomeomorph ω (wholePlaneBondEdgeEquiv D) = true
    rw [wholePlaneBondEdgeEquiv.apply_symm_apply]
    exact hq _ hf
  rw [wholePlaneDualConfigurationHomeomorph_bondState,hprimal,hoP] at hoQ
  cases hoQ

end
end PottsContinuity.PlanarTopology
