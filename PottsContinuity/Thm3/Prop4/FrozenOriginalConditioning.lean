module

public import PottsContinuity.PD.FK.ConditionalLaw
public import PottsContinuity.PD.FK.ProbabilityProduct
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Restoring the entire original sample from its normalized frozen fiber

The exact conditioning event fixes the open and closed states of every
revealed bond. Restoring those states recovers the full conditional law.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance originalConditioningEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Restoring a normalized frozen fiber gives the actual full FK law
conditioned on that original revealed state, on any finite graph. -/
theorem frozen_fiber_restore_eq_conditioned {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ : BoundaryCondition V) (R : Configuration G)
    (B : RemovedConfiguration G R) :
    (frozenFiberLaw θ ξ R B).map (fun A => A.val ∪ B.val) =
      (law G θ ξ).filter (frozenStateEvent R B) (frozenStateEvent_support θ ξ R B) := by
  classical
  let M := (law G θ ξ).filter (frozenStateEvent R B) (frozenStateEvent_support θ ξ R B)
  have hrem := law_filter_frozen_map_remaining θ ξ R B
  rw [← frozenFiberLaw_eq_remainingLaw] at hrem
  rw [← hrem,PMF.map_comp]
  change M.map _ = M
  calc
    _ = M.map id := by
      ext C
      simp only [PMF.map_apply]
      apply tsum_congr
      intro A
      by_cases hA : M A = 0
      · simp only [hA,ite_self]
      · have hstate : A ∩ R = B.val :=
          ((PMF.mem_support_filter_iff (frozenStateEvent_support θ ξ R B)).mp hA).1
        have hrestore : (configurationSplitEquiv G R A).1.val ∪ B.val = A := by
          change (A \ R) ∪ B.val = A
          rw [← hstate,Finset.sdiff_union_inter]
        simp only [Function.comp_apply,hrestore,id_eq]
        by_cases hCA : C = A <;> simp only [hCA,ite_true,ite_false]
    _ = _ := PMF.map_id M

end
end PottsContinuity.Thm3.Prop4
