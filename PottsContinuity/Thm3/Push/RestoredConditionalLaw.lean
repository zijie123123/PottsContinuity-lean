module

public import PottsContinuity.Thm3.Push.RemainingRestore
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance restoredLawEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance restoredLawRemainingFintype {V : Type*} [Finite V] (G : SimpleGraph V)
    (R : Configuration G) : Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- Mapping functions need agree only on configurations with positive mass. -/
theorem pmf_map_congr_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (hfg : ∀ a ∈ p.support, f a=g a) : p.map f=p.map g := by
  classical
  ext b
  rw [PMF.map_apply,PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a=0
  · simp only [ha,ite_self]
  · rw [hfg a ha]

/-- Putting the actual observed states back onto the remaining FK law gives
exactly the full original FK law conditioned on those states, not just its
remaining marginal. -/
theorem remainingLaw_map_restore_eq_filter {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (F : RemovedConfiguration G R) :
    (remainingLaw G θ (frozenBoundary ξ F.val) R).map (fun C => C.val ∪ F.val) =
    (law G θ ξ).filter (frozenStateEvent R F) (frozenStateEvent_support θ ξ R F) := by
  let μ := (law G θ ξ).filter (frozenStateEvent R F) (frozenStateEvent_support θ ξ R F)
  rw [← law_filter_frozen_map_remaining θ ξ R F,PMF.map_comp]
  calc
    μ.map ((fun C : RemainingConfiguration G R => C.val ∪ F.val) ∘
        (fun A => (configurationSplitEquiv G R A).1)) = μ.map id := by
      apply pmf_map_congr_on_support
      intro A hA
      have hstates := (PMF.mem_support_filter_iff _).mp hA |>.1
      change A ∩ R=F.val at hstates
      change (A \ R) ∪ F.val=A
      rw [← hstates]
      exact Finset.sdiff_union_inter A R
    _ = μ := PMF.map_id μ

/-- Exact conditional FULL law sampled on the ordinary deleted-edge graph
and restored through the inverse original FK split. -/
theorem edgeRestrictionLaw_map_restore_eq_filter {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (F : RemovedConfiguration G R) :
    (law (edgeRestriction G R) θ (frozenBoundary ξ F.val)).map
      (restoreRemainingConfiguration G R F) =
    (law G θ ξ).filter (frozenStateEvent R F) (frozenStateEvent_support θ ξ R F) := by
  calc
    (law (edgeRestriction G R) θ (frozenBoundary ξ F.val)).map
        (restoreRemainingConfiguration G R F) =
      ((law (edgeRestriction G R) θ (frozenBoundary ξ F.val)).map
        (edgeRestrictionConfigurationEquiv G R)).map (fun C => C.val ∪ F.val) := by
          rw [PMF.map_comp]
          rfl
    _ = (remainingLaw G θ (frozenBoundary ξ F.val) R).map (fun C => C.val ∪ F.val) := by
      rw [law_edgeRestriction_map]
    _ = _ := remainingLaw_map_restore_eq_filter G θ ξ R F

end
end PottsContinuity.Push
