module

public import PottsContinuity.DualityExt.PositiveEndpointDualSubgraphLaw
public import PottsContinuity.DualityExt.PositiveWiredDualSubgraphLaw
public import PottsContinuity.PD.Duality.FiniteDuality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Bridge the positive-parameter law to the PD finite FK law

For `q ≥ 1`, both APIs normalize the same finite FK weights. This module
provides the equality in the exact `PD.FK.law` type used by downstream
self-dual duality consumers.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The positive-`q` finite FK PMF agrees with the PD PMF whenever its
parameters lie in PD's range `q ≥ 1`, `0 < p < 1`. -/
theorem positiveFKLaw_eq_PD_law (θ : Parameters) (ξ : BoundaryCondition V) :
    positiveFKLaw G θ.val (edgeParameter θ) (clusterWeight_pos θ)
      (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξ = law G θ ξ := by
  classical
  let fPos : Fintype (Configuration G) :=
    PottsContinuity.DualityExt.positiveDMPConfigurationFintype
  let fPD : Fintype (Configuration G) :=
    @Finset.fintype G.edgeSet (PottsContinuity.PD.FK.edgeFintype G)
  have hweight (A : Configuration G) :
      positiveFKWeight G θ.val (edgeParameter θ) ξ A = weight G θ ξ A := by
    simp [positiveFKWeight, weight, edgeParameter]
  have hpartition :
      positiveFKPartitionFunction G θ.val (edgeParameter θ) ξ =
        partitionFunction G θ ξ := by
    change @FiniteProbability.partition (Configuration G) fPos
        (positiveFKWeight G θ.val (edgeParameter θ) ξ) =
      @FiniteProbability.partition (Configuration G) fPD (weight G θ ξ)
    calc
      @FiniteProbability.partition (Configuration G) fPos
          (positiveFKWeight G θ.val (edgeParameter θ) ξ) =
        @FiniteProbability.partition (Configuration G) fPos
          (fun A : Configuration G => weight G θ ξ A) := by
          congr 1
      _ = @FiniteProbability.partition (Configuration G) fPD (weight G θ ξ) :=
        @FiniteProbability.partition_equiv (Configuration G) (Configuration G)
          fPos fPD (Equiv.refl (Configuration G)) (weight G θ ξ)
  apply PMF.ext
  intro A
  rw [positiveFKLaw_apply (clusterWeight_pos θ) (edgeParameter_pos θ)
      (edgeParameter_lt_one θ) ξ A, law_apply]
  rw [positiveFKProbability, configurationProbability, hweight A, hpartition]

end
end PottsContinuity.DualityExt
