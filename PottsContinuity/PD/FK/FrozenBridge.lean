-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/FrozenBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.Model
public import PottsContinuity.PD.FK.ConfigurationBridge
public import PottsContinuity.PD.FK.WiredComponentBridge
public import PottsContinuity.PD.Defs.RCProb
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Exact finite-volume bridge to the frozen random-cluster probabilities

The graph is the frozen induced graph. Both boundary conditions use its entire
vertex carrier, so isolated vertices and boundary components are retained.
-/

@[expose] public section

namespace PottsContinuity.PD.FK

noncomputable section

/-- The admissible closed-interval edge parameter of an interior FK model. -/
def Parameters.toP (θ : Parameters) : Set.Icc (0 : ℝ) 1 :=
  ⟨edgeParameter θ, (edgeParameter_pos θ).le, (edgeParameter_lt_one θ).le⟩

/-- The positive cluster parameter of an FK model with cluster weight at least one. -/
def Parameters.toQ (θ : Parameters) : Set.Ioi (0 : ℝ) :=
  ⟨θ.val, clusterWeight_pos θ⟩

/-- The frozen vertex boundary, as a subset of the finite vertex carrier. -/
def frozenVertexBoundary (S : Finset (ℤ × ℤ)) : Set (S : Set (ℤ × ℤ)) :=
  {x | x.val ∈ vertexBoundary S}

/-- Free or wired boundary conditions, with exactly the frozen boundary vertices. -/
def frozenBoundaryCondition (S : Finset (ℤ × ℤ)) (i : Fin 2) :
    BoundaryCondition (S : Set (ℤ × ℤ)) :=
  if i = 0 then BoundaryCondition.free (frozenVertexBoundary S)
  else BoundaryCondition.wired (frozenVertexBoundary S)

theorem componentCount_wired_eq_rcWiredClusterCount (S : Finset (ℤ × ℤ))
    (ω : (PottsContinuity.PD.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    componentCount _ (BoundaryCondition.wired (frozenVertexBoundary S))
      (boolConfigurationEquiv _ ω) = rcWiredClusterCount S ω := by
  classical
  rw [componentCount_wired_eq_boundary_avoiding, rcOpenGraph_eq]
  unfold rcWiredClusterCount
  congr 1
  exact @ite_cond_congr ℕ _ _ _ _ 1 0 rfl

theorem componentCount_frozenBoundaryCondition (S : Finset (ℤ × ℤ)) (i : Fin 2)
    (ω : (PottsContinuity.PD.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    componentCount _ (frozenBoundaryCondition S i) (boolConfigurationEquiv _ ω) =
      if i = 0 then rcFreeClusterCount S ω else rcWiredClusterCount S ω := by
  unfold frozenBoundaryCondition
  split
  · exact componentCount_free_eq_rcFreeClusterCount S _ ω
  · exact componentCount_wired_eq_rcWiredClusterCount S ω

/-- The ported weight is exactly the frozen weight on the corresponding configuration. -/
theorem weight_eq_rcWeight (θ : Parameters) (S : Finset (ℤ × ℤ)) (i : Fin 2)
    (ω : (PottsContinuity.PD.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    weight _ θ (frozenBoundaryCondition S i) (boolConfigurationEquiv _ ω) =
      rcWeight S (edgeParameter θ) θ.val i ω := by
  unfold weight rcWeight
  rw [componentCount_frozenBoundaryCondition,
    ← closed_card_boolConfigurationEquiv, card_boolConfigurationEquiv]

open Classical in
/-- The two finite partition functions are equal, without any normalization factor. -/
theorem partitionFunction_eq_rcPartition (θ : Parameters) (S : Finset (ℤ × ℤ))
    (i : Fin 2) :
    partitionFunction (PottsContinuity.PD.squareLattice.induce
      (S : Set (ℤ × ℤ))) θ (frozenBoundaryCondition S i) =
      ∑ ω, rcWeight S (edgeParameter θ) θ.val i ω := by
  unfold partitionFunction FiniteProbability.partition
  symm
  refine Finset.sum_bij (fun ω _ => boolConfigurationEquiv _ ω) ?_ ?_ ?_ ?_
  · intro ω _
    simp only [Finset.mem_univ]
  · intro ω _ η _ h
    exact (boolConfigurationEquiv _).injective h
  · intro A _
    refine ⟨(boolConfigurationEquiv _).symm A, ?_,
      (boolConfigurationEquiv _).apply_symm_apply A⟩
    simp only [Finset.mem_univ]
  · intro ω _
    exact (weight_eq_rcWeight θ S i ω).symm

/-- Exact normalized probability bridge for arbitrary finite induced domains. -/
theorem configurationProbability_eq_rcProb (θ : Parameters) (S : Finset (ℤ × ℤ))
    (i : Fin 2)
    (ω : (PottsContinuity.PD.squareLattice.induce
      (S : Set (ℤ × ℤ))).edgeSet → Bool) :
    configurationProbability _ θ (frozenBoundaryCondition S i)
      (boolConfigurationEquiv _ ω) = rcProb S θ.toP θ.toQ i ω := by
  unfold configurationProbability rcProb
  rw [weight_eq_rcWeight, partitionFunction_eq_rcPartition]
  rfl

end

end PottsContinuity.PD.FK
