-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredVertexQuotientLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredVertexQuotient
public import PottsContinuity.FKC.FiniteFK.ProbabilityProduct

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}

local instance sourceEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance targetEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
local instance sourceConfigurationFintype : Fintype (Configuration G) := inferInstance
local instance targetConfigurationFintype : Fintype (Configuration H) := inferInstance

/-- The edge equivalence induces the exact bijection of finite configurations. -/
def wiredVertexQuotientConfigurationEquiv (E : G.edgeSet ≃ H.edgeSet) :
    Configuration G ≃ Configuration H := E.finsetCongr

omit [Finite V] [Finite W] in
@[simp] theorem wiredVertexQuotientConfigurationEquiv_apply
    (E : G.edgeSet ≃ H.edgeSet) (A : Configuration G) :
    wiredVertexQuotientConfigurationEquiv E A = A.map E.toEmbedding := rfl

theorem wiredVertexQuotient_weight_eq
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (q : ClusterWeight) (A : Configuration G) :
    weight G q ξ A =
      weight H q (BoundaryCondition.free (∅ : Set W)) (A.map E.toEmbedding) := by
  rw [weight, weight, Finset.card_map, Nat.card_congr E,
    wiredVertexQuotient_componentCount f hsurj E hE ξ hker A]

theorem wiredVertexQuotient_partitionFunction_eq
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (q : ClusterWeight) :
    partitionFunction G q ξ =
      partitionFunction H q (BoundaryCondition.free (∅ : Set W)) := by
  unfold partitionFunction FiniteProbability.partition
  rw [← (wiredVertexQuotientConfigurationEquiv E).sum_comp]
  apply Finset.sum_congr rfl
  intro A hA
  exact wiredVertexQuotient_weight_eq f hsurj E hE ξ hker q A

theorem wiredVertexQuotient_configurationProbability_eq
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (q : ClusterWeight) (A : Configuration G) :
    configurationProbability G q ξ A =
      configurationProbability H q (BoundaryCondition.free (∅ : Set W))
        (A.map E.toEmbedding) := by
  rw [configurationProbability, configurationProbability,
    wiredVertexQuotient_weight_eq f hsurj E hE ξ hker q A,
    wiredVertexQuotient_partitionFunction_eq f hsurj E hE ξ hker q]

/-- Exact transport of the whole finite FK law under the proved wired vertex quotient. -/
theorem wiredVertexQuotient_law_map
    (f : V → W) (hsurj : Function.Surjective f)
    (E : G.edgeSet ≃ H.edgeSet)
    (hE : ∀ e, (E e).val = Sym2.map f e.val)
    (ξ : BoundaryCondition V) (hker : ξ.partition = Setoid.ker f)
    (q : ClusterWeight) :
    (law G q ξ).map (fun A => A.map E.toEmbedding) =
      law H q (BoundaryCondition.free (∅ : Set W)) := by
  let e := wiredVertexQuotientConfigurationEquiv E
  change (law G q ξ).map e = law H q (BoundaryCondition.free (∅ : Set W))
  ext B
  obtain ⟨A, rfl⟩ := e.surjective B
  rw [FiniteProbability.map_equiv_apply, law_apply, law_apply,
    Equiv.symm_apply_apply]
  exact congrArg ENNReal.ofReal
    (wiredVertexQuotient_configurationProbability_eq f hsurj E hE ξ hker q A)

end
end PottsContinuity.FKC.FiniteFK
