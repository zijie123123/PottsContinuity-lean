-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteStatisticFrozenLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteConditionalEventBounds
public import PottsContinuity.FKC.FiniteFK.ConditionalLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance frozenStatisticEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance frozenStatisticEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance frozenStatisticConfigurationFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance frozenStatisticConfigurationNonempty : Nonempty (Configuration G) := ⟨∅⟩

/-- The complement of the block records precisely the edges whose states are observed. -/
def configurationOutsideBlock (F : Configuration G) : Configuration G :=
  Finset.univ \ F

/-- An attained outside-block record, viewed as an actual removed-edge state. -/
def configurationOutsideBlockState (F : Configuration G)
    (y : Set.range (fun A : Configuration G => A \ F)) :
    RemovedConfiguration G (configurationOutsideBlock F) := by
  refine ⟨y.1, ?_⟩
  obtain ⟨A, hA⟩ := y.2
  change A \ F = y.1 at hA
  intro e he
  change e ∈ y.1 at he
  rw [← hA] at he
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, (Finset.mem_sdiff.mp he).2⟩

/-- Removing a block is the same as retaining the open edges in its complement. -/
theorem configuration_sdiff_eq_inter_outside (F A : Configuration G) :
    A \ F = A ∩ configurationOutsideBlock F := by
  ext e
  simp [configurationOutsideBlock]

/-- Conditioning the actual FK law on the outside-block record is exactly its
literal frozen-state fiber on the complement edge set. -/
theorem finiteStatisticConditionalPMF_configurationOutsideBlock
    (q : ClusterWeight) (ξ : BoundaryCondition V) (F : Configuration G)
    (y : Set.range (fun A : Configuration G => A \ F)) :
    finiteStatisticConditionalPMF (law G q ξ)
        (fun A => (law_pos G q ξ A).ne') (fun A => A \ F) y =
      (law G q ξ).filter
        (frozenStateEvent (configurationOutsideBlock F)
          (configurationOutsideBlockState F y))
        (frozenStateEvent_support q ξ (configurationOutsideBlock F)
          (configurationOutsideBlockState F y)) := by
  classical
  have hfiber : {A : Configuration G | A \ F = y.1} =
      frozenStateEvent (configurationOutsideBlock F)
        (configurationOutsideBlockState F y) := by
    ext A
    change (A \ F = y.1) ↔
      A ∩ configurationOutsideBlock F = y.1
    rw [configuration_sdiff_eq_inter_outside]
  apply PMF.ext
  intro A
  simp only [finiteStatisticConditionalPMF, PMF.filter_apply, hfiber]

end
end PottsContinuity.FKC.FiniteFK
