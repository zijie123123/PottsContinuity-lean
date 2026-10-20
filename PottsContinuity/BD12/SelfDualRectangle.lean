module

public import PottsContinuity.PD.Duality.Parameters
public import PottsContinuity.PD.Duality.FiniteDuality
public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Actual rectangle duality at the formula value

Specializes the proved free/wired finite-law transport to the self-dual point.
This is a rectangle instance at p_sd, not a proof of duality at the genuine
critical threshold, nor a duality theorem for arbitrary boundary partitions.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.Duality

/-- The actual finite free law at the formula value pushes forward under
complementary-edge duality to the wired dual law at the same parameter.
The dual boundary includes the exterior face as in the PD rectangle model. -/
theorem rectangleLaw_selfDual (q : Set.Ici (1 : ℝ))
    (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) (criticalParameters q) (BoundaryCondition.free ∅)).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      law (rectangleDualGraph a w h) (criticalParameters q)
        (rectangleDualBoundaryCondition a w h) := by
  simpa only [dualParameters_criticalParameters] using
    rectangleFKLaw_map_primalDualConfigurationEquiv (criticalParameters q) a w h

end PottsContinuity.BD12
