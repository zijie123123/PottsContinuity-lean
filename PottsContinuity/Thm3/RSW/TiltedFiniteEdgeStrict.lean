module

public import PottsContinuity.PD.FK.FiniteEnergy
public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
open scoped BigOperators
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance tiltedStrictEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance tiltedStrictEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
local instance tiltedStrictRemainingFintype (e : G.edgeSet) :
    Fintype (RemainingConfiguration G {e}) := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

def strictRemovedBoolEquiv (e : G.edgeSet) :
    RemovedConfiguration G ({e} : Configuration G) ≃ Bool where
  toFun B := decide (e ∈ B.val)
  invFun b := if b then ⟨{e},by simp⟩ else ⟨∅,by simp⟩
  left_inv B := by
    apply Subtype.ext
    by_cases he : e ∈ B.val
    · have hB : B.val = {e} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨he,fun x hx => by simpa using B.property hx⟩
      simp [hB]
    · have hB : B.val = ∅ := by
        rcases Finset.subset_singleton_iff.mp B.property with h | h
        · exact h
        · exact (he (by simp [h])).elim
      simp [hB]
  right_inv b := by cases b <;> simp

def strictEdgeStateEquiv (e : G.edgeSet) :
    Configuration G ≃ RemainingConfiguration G ({e} : Configuration G) × Bool :=
  (configurationSplitEquiv G {e}).trans
    (Equiv.prodCongr (Equiv.refl _) (strictRemovedBoolEquiv G e))

omit [Finite V] in
@[simp] private theorem strictEdgeStateEquiv_false (e : G.edgeSet)
    (A : RemainingConfiguration G {e}) :
    (strictEdgeStateEquiv G e).symm (A,false) = A.val := by
  simp [strictEdgeStateEquiv,configurationSplitEquiv_symm_apply,strictRemovedBoolEquiv]

omit [Finite V] in
@[simp] private theorem strictEdgeStateEquiv_true (e : G.edgeSet)
    (A : RemainingConfiguration G {e}) :
    (strictEdgeStateEquiv G e).symm (A,true) = insert e A.val := by
  simp [strictEdgeStateEquiv,configurationSplitEquiv_symm_apply,strictRemovedBoolEquiv]

end
end PottsContinuity.RSW
