module

public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
local instance embeddedRevealEdgeDecidableEq {X : Type*} (K : SimpleGraph X) :
    DecidableEq K.edgeSet := Classical.decEq _

/-- Run an inner exploration on the actual restricted original states and
record those SAME bonds in the outer graph. Exterior edges are not revealed. -/
def embeddedReveal (reveal : RevealMap (G := G)) : RevealMap (G := H) :=
  fun A => (reveal (embeddedConfigurationRestriction G H f hGH A)).map
    (embeddedEdgeEmbedding G H f hGH)

omit [Finite V] [Finite W] in
@[simp] theorem mem_embeddedReveal_at_edge (reveal : RevealMap (G := G))
    (A : Configuration H) (e : G.edgeSet) :
    embeddedEdgeEmbedding G H f hGH e ∈ embeddedReveal G H f hGH reveal A ↔
      e ∈ reveal (embeddedConfigurationRestriction G H f hGH A) := by
  classical
  simp only [embeddedReveal,Finset.mem_map']

omit [Finite V] [Finite W] in
/-- Locality survives a literal graph embedding. Agreement on the lifted
record gives exactly the agreement needed by the inner stopping exploration. -/
theorem embeddedReveal_stable (reveal : RevealMap (G := G))
    (hstable : ∀ A B, B ∩ reveal A = A ∩ reveal A → reveal B = reveal A)
    (A B : Configuration H)
    (hagree : B ∩ embeddedReveal G H f hGH reveal A =
      A ∩ embeddedReveal G H f hGH reveal A) :
    embeddedReveal G H f hGH reveal B = embeddedReveal G H f hGH reveal A := by
  have hsmall : embeddedConfigurationRestriction G H f hGH B ∩
      reveal (embeddedConfigurationRestriction G H f hGH A) =
      embeddedConfigurationRestriction G H f hGH A ∩
      reveal (embeddedConfigurationRestriction G H f hGH A) := by
    ext e
    have hstates := Finset.ext_iff.mp hagree (embeddedEdgeEmbedding G H f hGH e)
    simpa only [Finset.mem_inter,mem_embeddedReveal_at_edge,
      mem_embeddedConfigurationRestriction] using hstates
  exact congrArg (fun R => R.map (embeddedEdgeEmbedding G H f hGH)) (hstable _ _ hsmall)

end
end PottsContinuity.Push
