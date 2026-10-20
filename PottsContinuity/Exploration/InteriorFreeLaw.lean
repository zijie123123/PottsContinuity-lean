module

public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Free FK law on a region after its exterior is frozen

If the revealed edge set is exactly the complement of an embedded finite
subgraph, the finite conditional embedded-law identity identifies the law on
that subgraph. When the induced boundary partition is discrete, this is the
free FK law. This theorem is a conditional interior-law statement: the frozen
exterior is a hypothesis. It is applied to attained selector fibres in
`Exploration.CircuitFiberFreeComparison`.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance interiorFreeLawOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance interiorFreeLawOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance interiorFreeLawInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance interiorFreeLawMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance interiorFreeLawRemainingFintype
    (R : Configuration H) : Fintype (RemainingConfiguration H R) := Fintype.ofFinite _
local instance interiorFreeLawRemovedFintype
    (R : Configuration H) : Fintype (RemovedConfiguration H R) := Fintype.ofFinite _

/-- After all non-interior edges of a finite graph are frozen, the conditional
law on the embedded inner graph is its free FK law whenever the pulled-back
frozen boundary partition identifies only equal vertices. The inner graph may
be any finite subgraph, and the parameter is an arbitrary `PD.FK.Parameters`.

The premise is stated on the actual induced partition from the record. In a
circuit application, `FiniteCircuitFreeBoundary` supplies it when the reveal
contains no edge internal to the circuit interior and the original boundary is
outside that interior. -/
theorem law_filter_frozen_map_embeddedRestriction_eq_free_of_discreteBoundary
    (θ : Parameters) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (hfree : ∀ x y : V,
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition.r x y ↔
        x = y) :
    ((law H θ ξ).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K)).map
        (embeddedConfigurationRestriction G H f hGH) =
      law G θ (BoundaryCondition.free
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).boundary) := by
  let η := isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)
  have hfreeη : ∀ x y : V, η.partition.r x y ↔ x = y := by
    intro x y
    simpa [η] using hfree x y
  have hη : η = BoundaryCondition.free η.boundary := by
    cases hη₀ : η with
    | mk boundary partition supported =>
      have hproj : η.partition = partition := congrArg BoundaryCondition.partition hη₀
      have hrel : ∀ x y, partition.r x y ↔ x = y := by
        intro x y
        rw [← hproj]
        exact hfreeη x y
      have hp : partition = ⊥ := Setoid.ext hrel
      cases hp
      rfl
  calc
    _ = law G θ η :=
      law_filter_frozen_map_embeddedRestriction G H f hGH θ ξ K
    _ = law G θ (BoundaryCondition.free η.boundary) := by
      rw [hη]
      rfl

end
end PottsContinuity.Exploration
