module

public import PottsContinuity.BD12.DRTHomogeneousIsomorphism
public import PottsContinuity.PD.FK.WiredBoxTranslation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Translation of arbitrary finite observables under actual homogeneous wired
box laws, using the shared exact boundary-partition transport. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section

/-- Actual homogeneous wired box expectations translate exactly. -/
theorem drtMean_wired_box_translation (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (a c : LatticeVertex) (r : ℕ)
    (f : Configuration (boxGraph (latticeTranslate a c) r) → ℝ) :
    drtMean (boxGraph (latticeTranslate a c) r) q
        (BoundaryCondition.wired (boxVertexBoundary (latticeTranslate a c) r))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β f =
      drtMean (boxGraph c r) q (BoundaryCondition.wired (boxVertexBoundary c r))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (fun A => f (configurationIso (boxVertexTranslationIso a c r) A)) := by
  have hi := drtMean_homogeneous_configurationIso q hq (boxVertexTranslationIso a c r)
    (BoundaryCondition.wired (boxVertexBoundary c r)) β f
  have hb : drtMean (boxGraph (latticeTranslate a c) r) q
      (BoundaryCondition.wired (boxVertexBoundary (latticeTranslate a c) r))
      (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β f =
      drtMean (boxGraph (latticeTranslate a c) r) q
      (boundaryConditionIso (boxVertexTranslationIso a c r) (BoundaryCondition.wired (boxVertexBoundary c r)))
      (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β f := by
    rw [drtMean_homogeneous_parameters_eq _ q hq, drtMean_homogeneous_parameters_eq _ q hq,
      law_eq_of_boundary_partition_eq (drtHomogeneousParameters q hq β) _ _
        (boundaryConditionIso_wired_box_partition a c r)]
  exact hb.trans hi

end
end PottsContinuity.BD12
