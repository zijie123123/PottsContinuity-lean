module

public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
local instance prewiredMarginalEdgeEq {V : Type*} (H : SimpleGraph V) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Omitting actual graph edges whose endpoints are already in one boundary
class leaves exactly the FK marginal on the retained original subgraph. -/
theorem law_map_subgraphRestriction_of_prewired
    {V : Type*} [Finite V] {G H : SimpleGraph V} (hGH : G ≤ H)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hwire : ∀ (u v : V) (huv : H.Adj u v),
      (⟨s(u,v),H.mem_edgeSet.mpr huv⟩ : H.edgeSet) ∈ subgraphRemovedEdges G H →
        ξ.partition.r u v) :
    (law H θ ξ).map (subgraphConfigurationRestriction hGH) = law G θ ξ := by
  classical
  let R := subgraphRemovedEdges G H
  have hremove := law_map_remove H θ ξ R hwire
  have hsub := law_subgraphRemaining_map hGH θ ξ
  calc
    _ = ((law H θ ξ).map (fun C => (configurationSplitEquiv H R C).1)).map
        (subgraphRemainingConfigurationEquiv hGH).symm := by
      rw [PMF.map_comp]
      congr 1
      funext C
      simpa only [Function.comp_apply,R] using
        (subgraphRemainingConfigurationEquiv_symm_split hGH C).symm
    _ = ((law G θ ξ).map (subgraphRemainingConfigurationEquiv hGH)).map
        (subgraphRemainingConfigurationEquiv hGH).symm := by rw [hremove,hsub]
    _ = _ := by
      rw [PMF.map_comp]
      have heq : (subgraphRemainingConfigurationEquiv hGH).symm ∘
          subgraphRemainingConfigurationEquiv hGH = id := by
        funext A
        exact Equiv.symm_apply_apply (subgraphRemainingConfigurationEquiv hGH) A
      rw [heq,PMF.map_id]

end
end PottsContinuity.RSW
