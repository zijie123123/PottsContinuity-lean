/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarDualLaw.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualConfiguration
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

local instance rectangleDoubleCollarDualLawOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualOuterGraph a w h).edgeSet := Classical.decEq _

local instance rectangleDoubleCollarDualLawInnerEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualInnerGraph a w h).edgeSet := Classical.decEq _

private theorem rectangleDoubleCollarDual_edgeRestriction_injective
    {V : Type*} (G : SimpleGraph V) (R S : Configuration G)
    (h : edgeRestriction G R = edgeRestriction G S) : R = S := by
  classical
  apply Finset.ext
  intro e
  have hs : G.edgeSet \ openEdges G R = G.edgeSet \ openEdges G S := by
    have hh := congrArg SimpleGraph.edgeSet h
    simpa only [edgeRestriction_edgeSet] using hh
  have ho : e.val ∈ openEdges G R ↔ e.val ∈ openEdges G S := by
    constructor
    · intro he
      by_contra hn
      have hm : e.val ∈ G.edgeSet \ openEdges G R := by
        simpa only [hs] using
          (show e.val ∈ G.edgeSet \ openEdges G S from ⟨e.property, hn⟩)
      exact hm.2 he
    · intro he
      by_contra hn
      have hm : e.val ∈ G.edgeSet \ openEdges G S := by
        simpa only [← hs] using
          (show e.val ∈ G.edgeSet \ openEdges G R from ⟨e.property, hn⟩)
      exact hm.2 he
  rw [← coe_mem_openEdges_iff G R e, ← coe_mem_openEdges_iff G S e]
  exact ho

private theorem rectangleDoubleCollarRemovedDualEdges_eq_subgraphRemoved
    (a : LatticeVertex) (w h : ℕ) :
    rectangleDoubleCollarRemovedDualEdges a w h =
      subgraphRemovedEdges
        ((rectangleDoubleCollarDualInnerGraph a w h).map
          (rectangleDoubleCollarDual_vertexEmbedding a w h))
        (rectangleDoubleCollarDualOuterGraph a w h) := by
  apply rectangleDoubleCollarDual_edgeRestriction_injective
  calc
    edgeRestriction (rectangleDoubleCollarDualOuterGraph a w h)
        (rectangleDoubleCollarRemovedDualEdges a w h) =
        rectangleDoubleCollarDualRemainingGraph a w h := rfl
    _ = _ := rectangleDoubleCollarDual_remainingGraph_eq_map_inner a w h
    _ = edgeRestriction (rectangleDoubleCollarDualOuterGraph a w h)
        (subgraphRemovedEdges
          ((rectangleDoubleCollarDualInnerGraph a w h).map
            (rectangleDoubleCollarDual_vertexEmbedding a w h))
          (rectangleDoubleCollarDualOuterGraph a w h)) := by
      symm
      exact edgeRestriction_subgraphRemovedEdges
        (rectangleDoubleCollarDual_map_le a w h)

/-- Conditioning the actual outer dual FK law on the selector-marked collar
edges being closed, then restricting to the embedded inner dual graph, gives
the actual inner dual FK law with the two vertical sides wired together. -/
theorem rectangleDoubleCollar_dualConditional_map
    (a : LatticeVertex) (w h : ℕ) (q : Parameters) :
    ((law (rectangleDoubleCollarDualOuterGraph a w h) q
        (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 2))).filter
      (frozenStateEvent (rectangleDoubleCollarRemovedDualEdges a w h)
        (rectangleDoubleCollarDualClosedState a w h))
      (frozenStateEvent_support q
        (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 2))
        (rectangleDoubleCollarRemovedDualEdges a w h)
        (rectangleDoubleCollarDualClosedState a w h))).map
      (embeddedConfigurationRestriction
        (rectangleDoubleCollarDualInnerGraph a w h)
        (rectangleDoubleCollarDualOuterGraph a w h)
        (rectangleDoubleCollarDual_vertexEmbedding a w h)
        (rectangleDoubleCollarDual_map_le a w h)) =
      law (rectangleDoubleCollarDualInnerGraph a w h) q
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)) := by
  let G := rectangleDoubleCollarDualInnerGraph a w h
  let H := rectangleDoubleCollarDualOuterGraph a w h
  let f := rectangleDoubleCollarDual_vertexEmbedding a w h
  let Rsel : Configuration H := rectangleDoubleCollarRemovedDualEdges a w h
  let Rstd : Configuration H := subgraphRemovedEdges (G.map f) H
  let Ksel : RemovedConfiguration H Rsel := rectangleDoubleCollarDualClosedState a w h
  let Kstd : RemovedConfiguration H Rstd := ⟨∅, Finset.empty_subset _⟩
  let ξ := rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 2)
  have hremoved : Rsel = Rstd := by
    simpa [Rsel, Rstd, G, H, f] using
      rectangleDoubleCollarRemovedDualEdges_eq_subgraphRemoved a w h
  have hevent : frozenStateEvent Rsel Ksel = frozenStateEvent Rstd Kstd := by
    ext C
    change C ∩ Rsel = ∅ ↔ C ∩ Rstd = ∅
    rw [hremoved]
  have hfilter : (law H q ξ).filter (frozenStateEvent Rsel Ksel)
      (frozenStateEvent_support q ξ Rsel Ksel) =
    (law H q ξ).filter (frozenStateEvent Rstd Kstd)
      (frozenStateEvent_support q ξ Rstd Kstd) := by
    ext C
    rw [PMF.filter_apply, PMF.filter_apply, hevent]
  have hcond := law_filter_frozen_map_embeddedRestriction G H f
    (rectangleDoubleCollarDual_map_le a w h) q ξ Kstd
  have hpart :
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ Kstd.val)).partition =
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)).partition := by
    apply Setoid.ext
    intro u v
    change (Setoid.comap f (componentSetoid H ξ Kstd.val)).r u v ↔ _
    change (Setoid.comap f (componentSetoid H ξ ∅)).r u v ↔ _
    rw [Setoid.comap_rel, componentSetoid_empty]
    change ξ.partition.r (f u) (f v) ↔ _
    exact rectangleDoubleCollarDual_outerBoundaryCondition_pullback a w h u v
  have hlaw := law_eq_of_boundary_partition_eq (G := G) q
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ Kstd.val))
    (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)) hpart
  calc
    ((law H q ξ).filter (frozenStateEvent Rsel Ksel)
        (frozenStateEvent_support q ξ Rsel Ksel)).map
        (embeddedConfigurationRestriction G H f
          (rectangleDoubleCollarDual_map_le a w h)) =
      ((law H q ξ).filter (frozenStateEvent Rstd Kstd)
        (frozenStateEvent_support q ξ Rstd Kstd)).map
        (embeddedConfigurationRestriction G H f
          (rectangleDoubleCollarDual_map_le a w h)) := by
            exact congrArg (fun μ => PMF.map
              (embeddedConfigurationRestriction G H f
                (rectangleDoubleCollarDual_map_le a w h)) μ) hfilter
    _ = law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ Kstd.val)) := by
      simpa [G, H, f, Rstd, ξ, Kstd] using hcond
    _ = law G q
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)) := hlaw

end
end PottsContinuity.PlanarMixed.Square
