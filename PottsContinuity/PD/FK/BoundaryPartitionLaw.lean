-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/BoundaryPartitionLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/RectangleBottomCollar.lean`.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q.
Only the general finite-graph declaration used by the box comparison is extracted. -/
module

public import PottsContinuity.PD.FK.PositiveAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.PD.FK

noncomputable section

theorem law_eq_of_boundary_partition_eq {V : Type*} [Finite V]
    {G : SimpleGraph V} (q : Parameters) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition = η.partition) : law G q ξ = law G q η := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : DecidableEq G.edgeSet := Classical.decEq _
  have hcount (A : Configuration G) :
      componentCount G ξ A = componentCount G η A := by
    simp only [componentCount, componentSetoid]
    rw [hξη]
  have hw (A : Configuration G) : weight G q ξ A = weight G q η A := by
    simp only [weight, hcount A]
  have hpartition : partitionFunction G q ξ = partitionFunction G q η := by
    unfold partitionFunction FiniteProbability.partition
    congr 1
    funext A
    exact hw A
  ext A
  rw [law_apply, law_apply, configurationProbability, configurationProbability,
    hw A, hpartition]

end
end PottsContinuity.PD.FK
