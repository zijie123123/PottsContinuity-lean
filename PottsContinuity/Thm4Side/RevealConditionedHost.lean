module

public import PottsContinuity.Thm4Side.AuxiliaryStatePartition
public import PottsContinuity.Thm4Side.DualRectangleReveal
public import PottsContinuity.Thm4.FKCProbabilityBridge

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.DualityExt
open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.PD.FK
open PottsContinuity.RSW

noncomputable section

local instance sideHostSourceEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance sideHostSourceConfigFintype (m : ℕ) :
    Fintype (PD.FK.Configuration (slitBoxGraph (16 * m))) := Fintype.ofFinite _

local instance sideHostResidualConfigFintype (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    Fintype (PD.FK.Configuration (PD.FK.edgeRestriction
      (slitBoxGraph (16 * m)) R)) :=
  Fintype.ofFinite _

local instance sideHostActiveConfigFintype (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    Fintype (PD.FK.Configuration (positiveActiveGraph
      (PD.FK.edgeRestriction (slitBoxGraph (16 * m)) R))) := Fintype.ofFinite _

abbrev SideStateHostVertex' (n : ℕ) :=
  RectangleVertex (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

abbrev SideStateHostGraph' (n : ℕ) :=
  rectangleGraph (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

local instance sideStateHostEdgeFintype' (n : ℕ) :
    Fintype (SideStateHostGraph' n).edgeSet := Fintype.ofFinite _

local instance sideStateHostEdgeDecidableEq' (n : ℕ) :
    DecidableEq (SideStateHostGraph' n).edgeSet := Classical.decEq _

abbrev sideRevealResidualGraph (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :=
  PD.FK.edgeRestriction (slitBoxGraph (16 * m)) R

noncomputable def sideRevealActiveHostEmbedding (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    positiveActiveVertexSet (sideRevealResidualGraph m R) ↪
      SideStateHostVertex' (16 * m) :=
  (positiveActiveInclusion (sideRevealResidualGraph m R)).trans
    (slitBoxAuxiliaryHostEmbedding (16 * m))

/-- The auxiliary ring and mapped open state of the right enlarged reveal,
viewed as a host removed-edge state. -/
noncomputable def slitRightDualRectangleHostRemovedState (m : ℕ)
    (X : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    PD.FK.RemovedConfiguration (SideStateHostGraph' (16 * m))
      (PD.FK.subgraphRemovedEdges
        ((positiveActiveGraph (sideRevealResidualGraph m
          (slitRightDualRectangleReveal m X))).map
          (sideRevealActiveHostEmbedding m
            (slitRightDualRectangleReveal m X)))
        (SideStateHostGraph' (16 * m))) := by
  let R := slitRightDualRectangleReveal m X
  let A := (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val
  refine ⟨slitBoxAuxiliaryArcRing (16 * m) ∪
    slitBoxAuxiliaryMapConfiguration (16 * m) A, ?_⟩
  simpa [sideRevealResidualGraph, sideRevealActiveHostEmbedding,
    SideStateHostGraph'] using
      (slitBoxAuxiliaryActiveRevealState_removed (16 * m) R A
        (revealRecordConfiguration (slitRightDualRectangleReveal m) X).property)

/-- The exact source-partition premise for the conditioned dual law of `DualityExt`, on the
right fixed reveal. -/
theorem slitRightDualRectangle_sourcePartition (m : ℕ)
    (X : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    (PD.FK.isolatedExtensionPullbackBoundary
      (positiveActiveInclusion
        (sideRevealResidualGraph m (slitRightDualRectangleReveal m X)))
      (PD.FK.frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (slitBoxBoundary (16 * m)))
        (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val)).partition =
    (PD.FK.isolatedExtensionPullbackBoundary
      (sideRevealActiveHostEmbedding m (slitRightDualRectangleReveal m X))
      (PD.FK.frozenBoundary (PD.FK.BoundaryCondition.free ∅)
        (slitRightDualRectangleHostRemovedState m X).val)).partition := by
  let R := slitRightDualRectangleReveal m X
  let A := (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val
  have h := slitBoxAuxiliaryActiveFrozenBoundary_partition_eq (16 * m) R A
  simpa [R, A, slitBoxBoundary,
    PottsContinuity.Thm4.fkcBoundaryToPD_wired,
    slitRightDualRectangleHostRemovedState, sideRevealActiveHostEmbedding,
    sideRevealResidualGraph, SideStateHostGraph'] using h.symm

end
end PottsContinuity.Thm4Side
