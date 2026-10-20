module

public import PottsContinuity.Thm4SideEuler.EmbeddedBoundaryLower
public import PottsContinuity.Thm4SideEuler.ResidualHostDualLaw
public import PottsContinuity.Thm4Side.ScreenSideStochasticDomination

@[expose] public section

namespace PottsContinuity.Thm4SideEuler

open MeasureTheory
open PottsContinuity.DualityExt
open PottsContinuity.Exploration
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm4
open PottsContinuity.Thm4Plane
open PottsContinuity.Thm4Side

noncomputable section

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance sideDomResidualEdgeFintype (m : ℕ) :
    Fintype (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance sideDomTargetEdgeFintype (m : ℕ) :
    Fintype (squareLattice.induce
      (slitRotatedPushRectangle m : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

local instance sideDomRightHostEdgeFintype (m : ℕ)
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    Fintype (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))).edgeSet :=
  Fintype.ofFinite _

local instance sideDomLeftHostEdgeFintype (m : ℕ)
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    Fintype (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitLeftDualRectangleReveal m X))).edgeSet :=
  Fintype.ofFinite _

local instance sideDomRightHostEdgeDecidableEq (m : ℕ)
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    DecidableEq (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))).edgeSet :=
  Classical.decEq _

local instance sideDomLeftHostEdgeDecidableEq (m : ℕ)
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    DecidableEq (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitLeftDualRectangleReveal m X))).edgeSet :=
  Classical.decEq _

/-- The target-edge configuration read from the retained host-dual carrier
`rectangleSubgraphDualGraph`
on the right fixed reveal. -/
noncomputable def slitRightResidualToHostDual (m : ℕ)
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    RemainingConfiguration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (slitRightDualRectangleReveal m X) →
      Configuration (rectangleSubgraphDualGraph
        (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))) :=
  ((edgeRestrictionConfigurationEquiv (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (slitRightDualRectangleReveal m X)).symm.trans
    ((positiveActiveConfigurationEquiv
        (edgeRestriction (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
          (slitRightDualRectangleReveal m X))).symm.trans
      ((isolatedExtensionConfigurationEquiv
          (positiveActiveGraph (edgeRestriction (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
            (slitRightDualRectangleReveal m X)))
          (sideExactLawHostEmbedding m (slitRightDualRectangleReveal m X))).trans
        (rectangleSubgraphDualConfigurationEquiv
          (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X)))))).toFun

/-- The right stopped law transported to the full retained host-dual graph
`rectangleSubgraphDualGraph`. -/
theorem slitRight_residual_hostDual_law_named (m : ℕ)
    (q : Set.Ici (1 : ℝ))
    (X : PD.FK.Configuration (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    (remainingLaw (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) (criticalParameters q)
      (frozenBoundary (fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val)
      (slitRightDualRectangleReveal m X)).map
        (slitRightResidualToHostDual m X) =
      law (rectangleSubgraphDualGraph
        (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X)))
        (criticalParameters q)
        (frozenBoundary
          (rectangleDualBoundaryCondition
            (-((16 * m + 1 : ℕ) : ℤ), -((16 * m + 1 : ℕ) : ℤ))
            (2 * (16 * m + 1)) (2 * (16 * m + 1)))
          (rectangleSubgraphDualOpenRemovedState
            (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))
            (slitRightDualRectangleHostRemovedState m X)).val) := by
  simpa [slitRightResidualToHostDual] using
    slitRight_residual_hostDual_law m q X

end
end PottsContinuity.Thm4SideEuler
