-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/CriticalEdgeToggle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SingleEdgeLaw
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance criticalEdgeToggleEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance criticalEdgeToggleEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance criticalEdgeToggleConfigurationFintype : Fintype (Configuration G) := Fintype.ofFinite _

/-- Flip one actual edge and leave every other edge state unchanged. -/
def toggleEdgeConfiguration (e : G.edgeSet) (A : Configuration G) : Configuration G :=
  if e ∈ A then A.erase e else insert e A

omit [Finite V] in
theorem toggleEdgeConfiguration_mem (e : G.edgeSet) (A : Configuration G) :
    e ∈ toggleEdgeConfiguration e A ↔ e ∉ A := by
  by_cases he : e ∈ A <;> simp [toggleEdgeConfiguration, he]

omit [Finite V] in
theorem toggleEdgeConfiguration_mem_of_ne {e f : G.edgeSet} (A : Configuration G)
    (hfe : f ≠ e) :
    f ∈ toggleEdgeConfiguration e A ↔ f ∈ A := by
  by_cases he : e ∈ A <;> simp [toggleEdgeConfiguration, he, hfe]

omit [Finite V] in
theorem toggleEdgeConfiguration_involutive (e : G.edgeSet) (A : Configuration G) :
    toggleEdgeConfiguration e (toggleEdgeConfiguration e A) = A := by
  by_cases he : e ∈ A <;> simp [toggleEdgeConfiguration, he]

def toggleEdgeConfigurationEquiv (e : G.edgeSet) : Configuration G ≃ Configuration G where
  toFun := toggleEdgeConfiguration e
  invFun := toggleEdgeConfiguration e
  left_inv := toggleEdgeConfiguration_involutive e
  right_inv := toggleEdgeConfiguration_involutive e

/-- For endpoints already identified by the wired component relation, opening a missing edge
multiplies its normalized FK mass by the critical odds `sqrt q`. -/
theorem configurationProbability_insert_eq_loopWeight_mul_of_related
    (q : ClusterWeight) (ξ : BoundaryCondition V) (A : Configuration G)
    {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hrelated : (componentSetoid G ξ A).r u v) :
    configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      loopWeight q * configurationProbability G q ξ A := by
  unfold configurationProbability
  rw [weight_insert_eq_loopWeight_mul_of_related q ξ A huv he hrelated]
  ring

/-- For endpoints in different wired components, opening a missing edge has reciprocal
critical odds. The relation here is the wired component relation, not actual path connectivity. -/
theorem configurationProbability_insert_mul_loopWeight_of_not_related
    (q : ClusterWeight) (ξ : BoundaryCondition V) (A : Configuration G)
    {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) * loopWeight q =
      configurationProbability G q ξ A := by
  unfold configurationProbability
  rw [div_mul_eq_mul_div,
    weight_insert_mul_loopWeight_of_not_related q ξ A huv he hne]

/-- Every finite complex sum is the average of the two terms in each edge-flip pair. -/
theorem sum_eq_average_toggle (e : G.edgeSet) (F : Configuration G → ℂ) :
    (∑ A : Configuration G, F A) =
      (1 / 2 : ℂ) * ∑ A : Configuration G, (F A + F (toggleEdgeConfiguration e A)) := by
  let E := toggleEdgeConfigurationEquiv e
  have hsum : (∑ A : Configuration G, F (E A)) = ∑ A : Configuration G, F A :=
    Equiv.sum_comp E F
  have hsum' : (∑ A : Configuration G, F (toggleEdgeConfiguration e A)) =
      ∑ A : Configuration G, F A := by
    change (∑ A : Configuration G, F (E A)) = _
    exact hsum
  calc
    (∑ A : Configuration G, F A) =
        (1 / 2 : ℂ) * ((∑ A : Configuration G, F A) +
          ∑ A : Configuration G, F (toggleEdgeConfiguration e A)) := by
      rw [hsum']
      ring
    _ = (1 / 2 : ℂ) *
        ∑ A : Configuration G, (F A + F (toggleEdgeConfiguration e A)) := by
      rw [Finset.sum_add_distrib]

end
end PottsContinuity.FKC.FiniteFK
